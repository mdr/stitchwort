//! `stitchwort-convert`: the one-off declaration-syntax converter
//! (docs/proposals/declaration-syntax.md §5). See the library for the rules.
//!
//! - `stitchwort-convert [PATH…]`: a dry run over `.sw` files, directories
//!   of them and `web/index.html` (its playground examples), printing what
//!   would change. With no paths: the prelude, `examples/`, `aoc/` and
//!   `web/index.html`, from the repository root.
//! - `--write`: write the converted files in place (the switch lane).
//! - `--print FILE`: print one file converted.
//! - `--stdin`: convert a snippet (a Rust test's source, a Markdown code
//!   block) from standard input to standard output; fails (exit 1, reason on
//!   standard error, nothing on standard output) if it can't.

use std::io::Read;
use std::path::{Path, PathBuf};
use std::process::ExitCode;

use clap::Parser;
use stitchwort_convert::{
    Report, convert_html, convert_module, convert_snippet, elaborated_arities,
};

#[derive(Parser)]
#[command(about = "Convert Stitchwort declarations to the def/theorem syntax")]
struct Args {
    /// Write converted files in place instead of reporting.
    #[arg(long)]
    write: bool,
    /// Print one file, converted, to standard output.
    #[arg(long, value_name = "FILE", conflicts_with_all = ["write", "stdin"])]
    print: Option<PathBuf>,
    /// Convert a snippet from standard input to standard output.
    #[arg(long, conflicts_with = "write")]
    stdin: bool,
    /// Files and directories (default: the repository's Stitchwort sources).
    paths: Vec<PathBuf>,
}

const DEFAULT_PATHS: [&str; 4] = [
    "crates/elab/src/prelude.sw",
    "examples",
    "aoc",
    "web/index.html",
];

fn main() -> ExitCode {
    let args = Args::parse();
    if args.stdin {
        let mut text = String::new();
        if let Err(e) = std::io::stdin().read_to_string(&mut text) {
            eprintln!("can't read standard input: {e}");
            return ExitCode::FAILURE;
        }
        return match convert_snippet(&text) {
            Ok(converted) => {
                print!("{}", converted.text);
                ExitCode::SUCCESS
            }
            Err(why) => {
                eprintln!("can't convert: {why}");
                ExitCode::FAILURE
            }
        };
    }
    if let Some(path) = args.print {
        let text = match std::fs::read_to_string(&path) {
            Ok(text) => text,
            Err(e) => {
                eprintln!("{}: {e}", path.display());
                return ExitCode::FAILURE;
            }
        };
        let result = if path.extension().is_some_and(|e| e == "html") {
            let (page, blocks) = convert_html(&text);
            match blocks.iter().find_map(|b| b.outcome.as_ref().err()) {
                Some(why) => Err(why.clone()),
                None => Ok(page),
            }
        } else {
            let arities = elaborated_arities(&text).ok();
            convert_module(&text, arities.as_ref()).map(|c| c.text)
        };
        return match result {
            Ok(text) => {
                print!("{text}");
                ExitCode::SUCCESS
            }
            Err(why) => {
                eprintln!("{}: {why}", path.display());
                ExitCode::FAILURE
            }
        };
    }

    let roots: Vec<PathBuf> = if args.paths.is_empty() {
        DEFAULT_PATHS.iter().map(PathBuf::from).collect()
    } else {
        args.paths
    };
    let mut files = Vec::new();
    for root in &roots {
        collect(root, &mut files);
    }
    files.sort();

    let mut total = Report::default();
    let mut converted = 0;
    let mut skipped: Vec<(String, String)> = Vec::new();
    let mut unchecked: Vec<String> = Vec::new();
    let mut completions: Vec<(String, usize, String, String)> = Vec::new();
    let mut bodiless: Vec<(String, usize, String)> = Vec::new();
    for path in &files {
        let shown = path.display().to_string();
        let text = match std::fs::read_to_string(path) {
            Ok(text) => text,
            Err(e) => {
                skipped.push((shown, e.to_string()));
                continue;
            }
        };
        if path.extension().is_some_and(|e| e == "html") {
            let (page, blocks) = convert_html(&text);
            let mut ok = true;
            for block in &blocks {
                let label = format!("{shown} #{}", block.id);
                match &block.outcome {
                    Ok(c) => {
                        converted += 1;
                        total.add(&c.report);
                        if !block.elaborated {
                            unchecked.push(label.clone());
                        }
                        for (line, name) in &c.report.bodiless {
                            bodiless.push((
                                shown.clone(),
                                block.first_line + line - 1,
                                name.clone(),
                            ));
                        }
                        for comp in &c.report.completions {
                            completions.push((
                                shown.clone(),
                                block.first_line + comp.line - 1,
                                comp.name.clone(),
                                comp.how.to_string(),
                            ));
                        }
                    }
                    Err(why) => {
                        ok = false;
                        skipped.push((label, why.clone()));
                    }
                }
            }
            if args.write && ok {
                write(path, &page, &mut skipped);
            }
            continue;
        }
        let arities = elaborated_arities(&text);
        match convert_module(&text, arities.as_ref().ok()) {
            Ok(c) => {
                converted += 1;
                total.add(&c.report);
                if arities.is_err() {
                    unchecked.push(shown.clone());
                }
                for (line, name) in &c.report.bodiless {
                    bodiless.push((shown.clone(), *line, name.clone()));
                }
                for comp in &c.report.completions {
                    completions.push((
                        shown.clone(),
                        comp.line,
                        comp.name.clone(),
                        comp.how.to_string(),
                    ));
                }
                if args.write {
                    write(path, &c.text, &mut skipped);
                }
            }
            Err(why) => skipped.push((shown, why)),
        }
    }

    println!(
        "{} {converted} of {} inputs ({} files; web/index.html counts each example)",
        if args.write {
            "Converted"
        } else {
            "Would convert"
        },
        converted + skipped.len(),
        files.len()
    );
    println!(
        "Declarations: {} ({} with a `:=` body, {} with arms; {} with named header parameters); tests: {}",
        total.declarations(),
        total.assign_form,
        total.arm_form,
        total.with_parameters,
        total.tests
    );
    let defs: std::collections::HashSet<(&String, &String)> =
        completions.iter().map(|(f, _, n, _)| (f, n)).collect();
    println!(
        "\nArms completed for exact arity: {} arms in {} definitions",
        completions.len(),
        defs.len()
    );
    for (file, line, name, how) in &completions {
        println!("  {file}:{line}  {name}: {how}");
    }
    println!(
        "\nSignatures without equations, written as a header with no body ({}):",
        bodiless.len()
    );
    for (file, line, name) in &bodiless {
        println!("  {file}:{line}  {name}");
    }
    println!(
        "\nArities counted from the written signature, because the input doesn't check ({}):",
        unchecked.len()
    );
    for label in &unchecked {
        println!("  {label}");
    }
    println!("\nNot converted ({}):", skipped.len());
    for (label, why) in &skipped {
        println!("  {label}: {why}");
    }
    if skipped.is_empty() {
        ExitCode::SUCCESS
    } else {
        ExitCode::FAILURE
    }
}

fn write(path: &Path, text: &str, skipped: &mut Vec<(String, String)>) {
    if let Err(e) = std::fs::write(path, text) {
        skipped.push((path.display().to_string(), format!("can't write: {e}")));
    }
}

/// `.sw` files under `path` (or `path` itself, if it's a file).
fn collect(path: &Path, files: &mut Vec<PathBuf>) {
    if path.is_file() {
        files.push(path.to_path_buf());
        return;
    }
    let Ok(entries) = std::fs::read_dir(path) else {
        return;
    };
    for entry in entries.flatten() {
        let p = entry.path();
        if p.is_dir() {
            collect(&p, files);
        } else if p.extension().is_some_and(|e| e == "sw") {
            files.push(p);
        }
    }
}
