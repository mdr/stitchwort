//! The language guide (`docs/guide/`): its examples are real, and what it
//! quotes is what the compiler says.
//!
//! - Every `.sw` file under `docs/guide/examples/` checks and passes its
//!   tests, except those in `errors/` (which must fail to check) and
//!   `failing/` (which check, and have a failing test). The project in
//!   `project/` checks and passes its tests.
//! - In the chapters, a fenced block right after `<!-- snippet: FILE -->`
//!   is that file, and one after `<!-- snippet: FILE#NAME -->` is the lines
//!   between `-- begin NAME` and `-- end NAME` in it (other such marker lines
//!   left out), and one after `<!-- snippet: FILE@A,B -->` is the top-level
//!   declarations `A` and `B`. `FILE` is relative to `docs/guide/examples/`,
//!   and may be outside it (`../../../aoc/…`).
//! - A fenced block right after `<!-- output: ARGS -->` is what
//!   `stitchwort ARGS` prints (standard output, then standard error), run in
//!   `docs/guide/examples/` without the cache; `ARGS` may end in `< FILE`
//!   for standard input. `<!-- generated: ARGS | FILE -->` runs
//!   `stitchwort ARGS -o DIR` and shows `DIR/FILE`. `<!-- node: SOURCE
//!   SCRIPT -->` builds `SOURCE` with `build --js`, and shows what `node
//!   SCRIPT` prints beside the module (not checked if `node` is missing).
//! - Every file in `errors/` and `failing/` is quoted by some `output`.
//!
//! `STITCHWORT_GUIDE_UPDATE=1 cargo test -p stitchwort-cli --test guide`
//! rewrites the quoted blocks from the files and the compiler instead of
//! comparing them; review the diff.

use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};

fn guide() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../docs/guide")
}

fn examples() -> PathBuf {
    guide().join("examples")
}

fn updating() -> bool {
    std::env::var("STITCHWORT_GUIDE_UPDATE").is_ok_and(|v| !v.is_empty())
}

/// Subcommands that take `--no-cache`.
const CACHED: [&str; 5] = ["check", "test", "run", "axioms", "build"];

/// The result of `stitchwort ARGS` in the examples folder: whether it
/// succeeded, and standard output followed by standard error.
fn stitchwort(args: &[&str], stdin: Option<&str>) -> (bool, String) {
    let mut command = Command::new(env!("CARGO_BIN_EXE_stitchwort"));
    command.args(args);
    if args.first().is_some_and(|c| CACHED.contains(c)) {
        command.arg("--no-cache");
    }
    command.current_dir(examples());
    match stdin {
        Some(file) => {
            let input = std::fs::File::open(examples().join(file)).expect("the input file");
            command.stdin(input);
        }
        None => {
            command.stdin(Stdio::null());
        }
    }
    let output = command.output().expect("run stitchwort");
    let mut text = String::from_utf8(output.stdout).unwrap();
    text.push_str(&String::from_utf8(output.stderr).unwrap());
    (output.status.success(), text)
}

/// The `.sw` files under `dir`, relative to the examples folder, sorted.
fn sw_files(dir: &Path, out: &mut Vec<String>) {
    for entry in std::fs::read_dir(dir).expect("a folder") {
        let path = entry.expect("an entry").path();
        if path.is_dir() {
            sw_files(&path, out);
        } else if path.extension().is_some_and(|e| e == "sw") {
            let relative = path.strip_prefix(examples()).unwrap();
            out.push(relative.to_string_lossy().replace('\\', "/"));
        }
    }
}

fn example_files() -> Vec<String> {
    let mut files = Vec::new();
    sw_files(&examples(), &mut files);
    files.sort();
    files
}

/// Lines with trailing spaces removed, and no blank lines at the end.
fn normalised(text: &str) -> String {
    let lines: Vec<&str> = text.lines().map(str::trim_end).collect();
    let end = lines
        .iter()
        .rposition(|l| !l.is_empty())
        .map_or(0, |i| i + 1);
    lines[..end].join("\n")
}

/// Whether `line` starts the top-level declaration called `name`.
fn declares(line: &str, name: &str) -> bool {
    let line = line.strip_prefix("export ").unwrap_or(line);
    [
        "def ",
        "theorem ",
        "type ",
        "instance ",
        "ability ",
        "interface ",
    ]
    .iter()
    .filter_map(|keyword| line.strip_prefix(keyword))
    .any(|rest| {
        rest.strip_prefix(name)
            .is_some_and(|after| after.starts_with([' ', ':', '(', '[']) || after.is_empty())
    })
}

/// The declarations called `names` (comma-separated) in `file`, each from its
/// first line to the last indented line after it, joined by blank lines.
fn declarations(file: &str, names: &str) -> String {
    let text = std::fs::read_to_string(examples().join(file))
        .unwrap_or_else(|e| panic!("snippet {file}@{names}: {e}"));
    let lines: Vec<&str> = text.lines().collect();
    let found: Vec<String> = names
        .split(',')
        .map(|name| {
            let name = name.trim();
            let start = lines
                .iter()
                .position(|l| declares(l, name))
                .unwrap_or_else(|| panic!("snippet {file}@{names}: no declaration `{name}`"));
            // A declaration's own lines are indented, or a `:=` line in
            // column 0 after `decreasing`, or a closing bracket in column 0;
            // blank lines inside it are kept.
            let mut end = start + 1;
            let mut last = start;
            while end < lines.len() {
                let line = lines[end];
                if line.trim().is_empty() {
                    end += 1;
                } else if line.starts_with([' ', '}', ')', ']']) || line.starts_with(":=") {
                    last = end;
                    end += 1;
                } else {
                    break;
                }
            }
            lines[start..=last].join("\n")
        })
        .collect();
    found.join("\n\n")
}

/// The text a snippet marker names: a whole file, one region of it
/// (`FILE#NAME`), or some of its declarations (`FILE@NAME,NAME`).
fn snippet(target: &str) -> String {
    if let Some((file, names)) = target.split_once('@') {
        return declarations(file, names);
    }
    let (file, region) = match target.split_once('#') {
        Some((file, region)) => (file, Some(region)),
        None => (target, None),
    };
    let text = std::fs::read_to_string(examples().join(file))
        .unwrap_or_else(|e| panic!("snippet {target}: {e}"));
    let marker = |l: &str| {
        let t = l.trim_start();
        t.starts_with("-- begin ") || t.starts_with("-- end ")
    };
    let Some(region) = region else {
        return text
            .lines()
            .filter(|l| !marker(l))
            .collect::<Vec<_>>()
            .join("\n");
    };
    let begin = format!("-- begin {region}");
    let end = format!("-- end {region}");
    let mut inside = false;
    let mut found = false;
    let mut lines = Vec::new();
    for line in text.lines() {
        let t = line.trim();
        if t == begin {
            inside = true;
            found = true;
        } else if t == end {
            inside = false;
        } else if inside && !marker(line) {
            lines.push(line);
        }
    }
    assert!(found, "snippet {target}: no `{begin}` in {file}");
    lines.join("\n")
}

/// What an `output` or `generated` marker shows.
fn output(kind: &str, spec: &str) -> String {
    match kind {
        "output" => {
            let (args, stdin) = match spec.split_once(" < ") {
                Some((args, file)) => (args, Some(file.trim())),
                None => (spec, None),
            };
            let args: Vec<&str> = args.split_whitespace().collect();
            stitchwort(&args, stdin).1
        }
        "generated" => {
            let (args, file) = spec.split_once(" | ").expect("`generated: ARGS | FILE`");
            let out = std::env::temp_dir().join(format!("stitchwort-guide-{}", std::process::id()));
            let _ = std::fs::remove_dir_all(&out);
            let out_text = out.display().to_string();
            let mut args: Vec<&str> = args.split_whitespace().collect();
            args.extend(["-o", &out_text]);
            let (ok, printed) = stitchwort(&args, None);
            assert!(ok, "generated: {spec}:\n{printed}");
            let text = std::fs::read_to_string(out.join(file.trim()))
                .unwrap_or_else(|e| panic!("generated: {spec}: {e}"));
            let _ = std::fs::remove_dir_all(&out);
            text
        }
        _ => unreachable!(),
    }
}

/// What `node SCRIPT` prints, beside the module `stitchwort build --js
/// SOURCE` writes (`node: SOURCE SCRIPT`); `None` without `node`.
fn node_output(spec: &str) -> Option<String> {
    let (source, script) = spec.split_once(' ').expect("`node: SOURCE SCRIPT`");
    let out = std::env::temp_dir().join(format!("stitchwort-guide-node-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&out);
    let out_text = out.display().to_string();
    let (ok, printed) = stitchwort(&["build", "--js", source, "-o", &out_text], None);
    assert!(ok, "node: {spec}:\n{printed}");
    let script = script.trim();
    std::fs::copy(examples().join(script), out.join(script)).expect("copy the script");
    let ran = Command::new("node")
        .arg(script)
        .current_dir(&out)
        .stdin(Stdio::null())
        .output();
    let _ = std::fs::remove_dir_all(&out).ok();
    let Ok(ran) = ran else {
        eprintln!("node isn't available: `node: {spec}` not checked");
        return None;
    };
    let mut text = String::from_utf8(ran.stdout).unwrap();
    text.push_str(&String::from_utf8(ran.stderr).unwrap());
    Some(text)
}

/// A marker comment on `line`: `(kind, argument)`.
fn marker(line: &str) -> Option<(&str, &str)> {
    let inner = line
        .trim()
        .strip_prefix("<!--")?
        .strip_suffix("-->")?
        .trim();
    let (kind, rest) = inner.split_once(':')?;
    let kind = kind.trim();
    ["snippet", "output", "generated", "node"]
        .contains(&kind)
        .then(|| (kind, rest.trim()))
}

/// Checks (or, when updating, rewrites) the quoted blocks of one chapter.
/// Gives the problems found, and the `output` arguments it saw.
fn chapter(path: &Path, outputs: &mut Vec<String>) -> Vec<String> {
    let text = std::fs::read_to_string(path).expect("a chapter");
    let name = path.file_name().unwrap().to_string_lossy().into_owned();
    let lines: Vec<&str> = text.lines().collect();
    let mut problems = Vec::new();
    let mut rewritten: Vec<String> = Vec::new();
    let mut i = 0;
    while i < lines.len() {
        rewritten.push(lines[i].to_string());
        let Some((kind, spec)) = marker(lines[i]) else {
            i += 1;
            continue;
        };
        let at = i + 1;
        let open = lines.get(at).copied().unwrap_or("");
        if !open.starts_with("```") {
            problems.push(format!(
                "{name}:{at}: a {kind} marker must be followed by a fenced block"
            ));
            i += 1;
            continue;
        }
        let close = (at + 1..lines.len())
            .find(|&j| lines[j].trim_end() == "```")
            .unwrap_or_else(|| panic!("{name}:{at}: the block never closes"));
        let quoted = lines[at + 1..close].join("\n");
        if kind == "output" {
            outputs.push(spec.to_string());
        }
        let expected = match kind {
            "snippet" => snippet(spec),
            "node" => node_output(spec).unwrap_or_else(|| quoted.clone()),
            _ => output(kind, spec),
        };
        if normalised(&quoted) != normalised(&expected) {
            problems.push(format!(
                "{name}:{}: the block after `{kind}: {spec}` differs.\n--- quoted\n{}\n--- actual\n{}\n",
                at + 1,
                normalised(&quoted),
                normalised(&expected)
            ));
        }
        rewritten.push(open.to_string());
        rewritten.push(normalised(&expected));
        rewritten.push("```".to_string());
        i = close + 1;
    }
    if updating() {
        let mut new = rewritten.join("\n");
        new.push('\n');
        if new != text {
            std::fs::write(path, new).expect("rewrite the chapter");
        }
        return Vec::new();
    }
    problems
}

#[test]
fn the_guide_quotes_its_examples_and_the_compiler() {
    let mut chapters: Vec<PathBuf> = std::fs::read_dir(guide())
        .expect("docs/guide")
        .map(|e| e.expect("an entry").path())
        .filter(|p| p.extension().is_some_and(|e| e == "md"))
        .collect();
    chapters.sort();
    assert!(chapters.len() >= 10, "{chapters:?}");

    let mut outputs = Vec::new();
    let problems: Vec<String> = chapters
        .iter()
        .flat_map(|path| chapter(path, &mut outputs))
        .collect();
    assert!(problems.is_empty(), "{}", problems.join("\n"));

    // Every example that is there to fail is shown failing.
    for file in example_files() {
        if file.starts_with("errors/") || file.starts_with("failing/") {
            assert!(
                outputs
                    .iter()
                    .any(|o| o.split_whitespace().any(|w| w == file)),
                "{file} is never quoted by an `output` marker"
            );
        }
    }
}

/// What is wrong with one example file, if anything.
fn example_problem(file: &str) -> Option<String> {
    let (checked, printed) = stitchwort(&["check", file], None);
    if file.starts_with("errors/") {
        return checked.then(|| format!("{file} should fail to check, but checks"));
    }
    if !checked {
        return Some(format!("{file} should check:\n{printed}"));
    }
    let text = std::fs::read_to_string(examples().join(file)).unwrap();
    if !text.lines().any(|l| l.starts_with("test ")) {
        return None;
    }
    let (passed, printed) = stitchwort(&["test", file], None);
    match (file.starts_with("failing/"), passed) {
        (false, false) => Some(format!("{file}: its tests should pass:\n{printed}")),
        (true, true) => Some(format!("{file}: a test should fail, but all pass")),
        _ => None,
    }
}

#[test]
fn the_guide_examples_check_and_pass_their_tests() {
    let files: Vec<String> = example_files()
        .into_iter()
        .filter(|f| !f.starts_with("project/"))
        .collect();
    assert!(files.len() >= 10, "{files:?}");
    let problems: Vec<String> = std::thread::scope(|scope| {
        let handles: Vec<_> = files
            .chunks(files.len().div_ceil(4))
            .map(|chunk| {
                scope.spawn(move || {
                    chunk
                        .iter()
                        .filter_map(|f| example_problem(f))
                        .collect::<Vec<_>>()
                })
            })
            .collect();
        handles
            .into_iter()
            .flat_map(|h| h.join().unwrap())
            .collect()
    });
    assert!(problems.is_empty(), "{}", problems.join("\n"));
}

#[test]
fn the_guide_project_checks_and_passes_its_tests() {
    let (passed, printed) = stitchwort(&["test", "--project", "project"], None);
    assert!(passed, "{printed}");
}
