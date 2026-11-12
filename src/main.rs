// TODO:
// - Reduce the number of potential false positives by skipping non-pub methods.

use std::collections::{HashMap, HashSet};
use std::env;
use std::fs;
use std::io::BufReader;
use std::path::PathBuf;
use std::process;
use std::time::{SystemTime, UNIX_EPOCH};

use clap::Parser;
use colored::Colorize;
use itertools::Itertools;
use log::*;
use protobuf::Message;
use scip::types::{Index, Occurrence, SymbolInformation, SymbolRole, symbol_information::Kind};

#[derive(Parser)]
#[command(name = "cargo")]
#[command(bin_name = "cargo")]
enum MainFlags {
    Unused(Flags),
}

/// Detect unused pub methods in a workspace.
#[derive(clap::Args)]
#[command(version, about)]
struct Flags {
    #[clap(default_value_os_t = std::env::current_dir().unwrap())]
    workspace: PathBuf,
    #[clap(long)]
    scip: Option<PathBuf>,
    #[clap(long, value_delimiter = ',', default_value = "rs,html")]
    extensions: Vec<String>,
}

/// Returns whether a SCIP symbol denotes a trait method declaration.
///
/// rust-analyzer declares a trait method as `.../Trait#method()`, whereas an impl
/// method is `.../impl#[Type]method()` (the `impl#[` marker itself contains a `#`,
/// hence the extra guard). Trait methods may be called implicitly, so they are
/// skipped rather than reported.
fn is_trait_method(symbol: &str) -> bool {
    symbol.contains('#') && !symbol.contains("impl#[")
}

/// Returns whether a SCIP symbol denotes a trait method implementation.
///
/// rust-analyzer emits symbols shaped as:
/// - inherent method: `.../impl#[Type]method().`
/// - trait method:    `.../impl#[Type][Trait]method().`
///
/// Trait methods may be called implicitly (e.g. serde's `Visitor`), and their
/// trait often lives outside the workspace, so it never enters the `traits` set
/// collected from the index; matching by trait name therefore misses them. Detect
/// them structurally instead: after `impl#[`, skip the first bracketed segment
/// (the type) and check whether another `[` immediately follows.
fn is_trait_impl(symbol: &str) -> bool {
    const MARK: &str = "impl#[";
    let Some(pos) = symbol.find(MARK) else {
        return false;
    };
    let rest = &symbol[pos + MARK.len()..];
    // Skip the first segment (the type); the type itself may contain brackets,
    // so match them by nesting depth.
    let mut depth = 1usize;
    for (i, c) in rest.char_indices() {
        match c {
            '[' => depth += 1,
            ']' => {
                depth -= 1;
                if depth == 0 {
                    return rest[i + 1..].starts_with('[');
                }
            }
            _ => {}
        }
    }
    false
}

/// Path to a fresh temporary file inside the system temp directory.
fn temp_path(ext: &str) -> PathBuf {
    let nanos = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map(|d| d.as_nanos())
        .unwrap_or(0);
    env::temp_dir().join(format!("cargo-unused-{}-{}.{}", process::id(), nanos, ext))
}

/// Removes a generated temporary file (SCIP index or config) when dropped.
struct TempFile(PathBuf);

impl Drop for TempFile {
    fn drop(&mut self) {
        let _ = fs::remove_file(&self.0);
    }
}

/// rust-analyzer settings used when generating the index: index only the default
/// cargo targets and leave `cfg(test)` off. Much faster, and test-declared
/// methods are dropped in Pass 2 anyway.
const RA_CONFIG: &str = r#"{"cargo":{"allTargets":false},"cfg":{"setTest":false}}"#;

fn main_impl(args: MainFlags) -> anyhow::Result<()> {
    let MainFlags::Unused(args) = args;
    env_logger::Builder::from_env(env_logger::Env::default().default_filter_or("info")).init();

    if !args.workspace.join("Cargo.toml").exists() {
        anyhow::bail!("{:?} does not contain a Cargo.toml file", args.workspace);
    }

    // No manual SCIP step needed: unless `--scip` points at an existing index,
    // generate one automatically. The default index goes to the system temp
    // directory so the workspace is never polluted with an `index.scip` file.
    let scip = args.scip.clone().unwrap_or_else(|| temp_path("scip"));
    let _temp_scip = args.scip.is_none().then(|| TempFile(scip.clone()));
    if !scip.exists() {
        let config = temp_path("json");
        fs::write(&config, RA_CONFIG)?;
        let _temp_config = TempFile(config.clone());
        info!(
            "Generating SCIP index with rust-analyzer into {:?}. This may take a while for large workspaces.",
            scip
        );
        duct::cmd!(
            "rust-analyzer",
            "scip",
            &args.workspace,
            "--output",
            &scip,
            "--config-path",
            &config
        )
        .dir(&args.workspace)
        .stdout_null()
        .stderr_null()
        .run()?;
    }
    info!("Running on {:?} with SCIP {:?}", args.workspace, scip);

    // Parse SCIP
    let reader = fs::File::open(scip)?;
    let mut reader = BufReader::new(reader);
    let index = Index::parse_from_reader(&mut reader)?;
    debug!("Opened SCIP file with {} documents", index.documents.len());

    // Record method/function declarations, plus the document each is declared in
    // (used to drop methods declared in test files).
    let mut declarations = HashMap::<&String, &SymbolInformation>::default();
    let mut decl_paths = HashMap::<&str, &str>::default();
    for doc in &index.documents {
        for s in &doc.symbols {
            let Ok(kind) = s.kind.enum_value() else {
                continue;
            };
            if kind != Kind::Method && kind != Kind::Function {
                continue;
            }
            declarations.insert(&s.symbol, s);
            decl_paths.insert(s.symbol.as_str(), doc.relative_path.as_str());
        }
    }
    debug!("Found {} declarations", declarations.len());

    // Single pass over occurrences: remember each symbol's definition position and
    // drop declarations that are referenced anywhere in the workspace.
    let mut def_occ = HashMap::<&str, (&str, &Occurrence)>::default();
    for doc in &index.documents {
        for o in &doc.occurrences {
            if (o.symbol_roles & SymbolRole::Definition as i32) > 0 {
                def_occ
                    .entry(o.symbol.as_str())
                    .or_insert((doc.relative_path.as_str(), o));
            } else {
                declarations.remove(&o.symbol);
            }
        }
    }

    debug!("Pass 1: {} candidates", declarations.len());

    // Pass 2
    // Remove mains (which are never called)
    //        methods in tests (test methods are never called)
    //        trait methods (which may be called implicitly)
    // TODO: For the first two, only remove #[test] and #[main], #[tokio::main] methods.
    declarations.retain(|_, d| {
        !d.symbol.contains("test")
            && d.display_name != "main"
            // Skip methods declared in test files (paths such as `tests/…`).
            && decl_paths
                .get(d.symbol.as_str())
                .is_none_or(|p| !p.contains("test"))
            // Trait methods are called implicitly: declaration methods are
            // `Trait#method()`, impl methods are `impl#[Type][Trait]method()`.
            && !is_trait_method(&d.symbol)
            && !is_trait_impl(&d.symbol)
    });
    debug!(
        "Pass 2 (mains, tests, trait methods): {} candidates",
        declarations.len()
    );
    if declarations.is_empty() {
        info!("Found 0 possibly unused functions");
        return Ok(());
    }

    // Pass 3: Grep for candidates. Index candidate names by their display name so
    // each line is tokenized once instead of scanned against every declaration
    // (O(tokens) rather than O(lines × declarations)).
    let by_name = declarations
        .values()
        .map(|d| (d.display_name.as_str(), &d.symbol))
        .into_group_map();
    let mut counts = HashMap::<&String, usize>::default();
    let mut seen = HashSet::<&String>::default();
    let extensions: HashSet<String> = args.extensions.into_iter().collect();
    walkdir::WalkDir::new(&args.workspace)
        .min_depth(1)
        .into_iter()
        .filter_entry(|e| !e.path().join("CACHEDIR.TAG").exists())
        .filter_map(|e| e.ok())
        .filter(|f| {
            f.file_type().is_file()
                && f.path()
                    .extension()
                    .and_then(|f| f.to_str())
                    .is_some_and(|e| extensions.contains(e))
        })
        .for_each(|f| {
            let Ok(contents) = fs::read_to_string(f.path()) else {
                return;
            };
            for line in contents.lines() {
                seen.clear();
                for tok in line.split(|c: char| !(c.is_alphanumeric() || c == '_')) {
                    if let Some(syms) = by_name.get(tok) {
                        for s in syms {
                            // Count each line once per candidate, as before.
                            if seen.insert(*s) {
                                *counts.entry(*s).or_default() += 1;
                            }
                        }
                    }
                }
            }
        });
    declarations.retain(|sym, _| counts.get(sym).copied().unwrap_or_default() <= 1);
    debug!("Pass 3 (search): {} candidates", declarations.len());
    let n_found = declarations.len();
    info!("Found {} possibly unused functions", n_found);

    // Group the surviving candidates by file, using the definition positions
    // recorded during the single occurrence pass above.
    let mut by_file = declarations
        .keys()
        .filter_map(|sym| def_occ.get(sym.as_str()))
        .map(|(path, occ)| (*path, *occ))
        .into_group_map()
        .into_iter()
        .collect_vec();
    by_file.sort_by_key(|(path, _)| *path);
    // Display
    for (path, mut occs) in by_file {
        let full_path = args.workspace.join(path);
        if !full_path.exists() {
            warn!("{} not found, is the SCIP file up-to-date?", path);
            continue;
        }
        let lines = fs::read_to_string(full_path)?;
        let lines: Vec<&str> = lines.lines().collect();
        occs.sort_by_key(|occ| occ.range[0]);
        println!("{}", path.yellow());
        for occ in occs {
            let line = occ.range[0] as usize;
            println!("{:<4} {}", (line + 1).to_string().blue(), lines[line]);
        }
        println!();
    }
    anyhow::ensure!(n_found == 0, "Found {} possibly unused functions", n_found);
    Ok(())
}

fn main() {
    if let Err(e) = main_impl(MainFlags::parse()) {
        error!("{}", e);
        process::exit(2);
    }
}
