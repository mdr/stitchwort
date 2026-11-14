//! Helpers shared by the CLI's test binaries.

#![allow(dead_code)] // each test binary uses some of these

use std::path::Path;
use std::process::Command;

/// The test binary's `stitchwort` command for `subcommand`, with `--native`
/// added after `run` and `build` when `STITCHWORT_TEST_RUN=native`
/// (docs/reviews/SW-2535-native-default-plan.md, N5a). Unset or `machine`
/// leaves them as they are.
///
/// Use [`cli_plain`] for a run that names its own backend (`--js`,
/// `--reference`) or needs the machine (`--profile`, `--alloc-trace`):
/// `--native` conflicts with those.
pub fn cli(subcommand: &str) -> Command {
    let mut command = cli_plain(subcommand);
    if matches!(subcommand, "run" | "build") && native_wanted() {
        command.arg("--native");
    }
    command
}

/// [`cli`] with `flags` after the subcommand, except that a run which names
/// its own backend (`--js`, `--reference`, `--native`) or needs the machine
/// (`--profile`, `--alloc-trace`) stays as written.
pub fn cli_with(subcommand: &str, flags: &[&str]) -> Command {
    let own = |flag: &&str| {
        matches!(
            *flag,
            "--js" | "--reference" | "--native" | "--profile" | "--alloc-trace"
        )
    };
    let mut command = if flags.iter().any(own) {
        cli_plain(subcommand)
    } else {
        cli(subcommand)
    };
    command.args(flags);
    command
}

/// The test binary's `stitchwort` command for `subcommand`, whatever
/// `STITCHWORT_TEST_RUN` says.
pub fn cli_plain(subcommand: &str) -> Command {
    let mut command = Command::new(env!("CARGO_BIN_EXE_stitchwort"));
    command.arg(subcommand);
    command
}

/// Whether `STITCHWORT_TEST_RUN` is `native`; unset or `machine` is not.
/// Anything else is a typo, and fails rather than quietly testing the
/// machine.
pub fn native_wanted() -> bool {
    match std::env::var("STITCHWORT_TEST_RUN").as_deref() {
        Err(_) | Ok("") | Ok("machine") => false,
        Ok("native") => true,
        Ok(other) => panic!("STITCHWORT_TEST_RUN={other}: expected `native` or `machine`"),
    }
}

/// Every name `EXAMPLES` can match: the `.sw` files in every folder under
/// `examples/` (except `examples/projects`), and every project folder under
/// `examples/projects/*/`.
///
/// Every test binary checks its filter against this same set, so a part that
/// names an example another binary sweeps still counts here.
pub fn all_names() -> Vec<String> {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../examples");
    let mut names = Vec::new();
    sw_files(&root, &mut names);
    let Ok(kinds) = std::fs::read_dir(root.join("projects")) else {
        return names;
    };
    for kind in kinds {
        let kind = kind.expect("readable directory entry").path();
        let Ok(projects) = std::fs::read_dir(kind) else {
            continue;
        };
        names.extend(
            projects
                .map(|entry| entry.expect("readable directory entry").path())
                .filter(|path| path.is_dir())
                .map(|path| path.file_name().unwrap().to_string_lossy().into_owned()),
        );
    }
    names
}

/// Adds the `.sw` file names under `dir` to `names`, recursively, skipping
/// `examples/projects` (projects match by folder name instead).
fn sw_files(dir: &Path, names: &mut Vec<String>) {
    let Ok(entries) = std::fs::read_dir(dir) else {
        return;
    };
    for entry in entries {
        let path = entry.expect("readable directory entry").path();
        if path.is_dir() {
            if path.file_name().is_some_and(|name| name == "projects") {
                continue;
            }
            sw_files(&path, names);
        } else if path.extension().is_some_and(|ext| ext == "sw") {
            names.push(path.file_name().unwrap().to_string_lossy().into_owned());
        }
    }
}

/// The non-empty parts of an `EXAMPLES` filter, in order.
fn parts(filter: &str) -> impl Iterator<Item = &str> {
    filter
        .split(',')
        .map(str::trim)
        .filter(|part| !part.is_empty())
}

/// Fails when `EXAMPLES` is set and one of its parts matches none of `names`.
///
/// `EXAMPLES` keeps the names containing a part, so a part that matches
/// nothing runs no tests and passes silently: the nearest names turn a typo
/// into a failure that says what it meant. `names` is every name the binary
/// would check, so a part that only matches in another test's sweep still
/// counts.
pub fn check_examples_env(names: &[String], noun: &str) {
    let Ok(filter) = std::env::var("EXAMPLES") else {
        return;
    };
    if let Some(message) = filter_error(&filter, names, noun) {
        panic!("{message}");
    }
}

/// The message to fail with when an `EXAMPLES` part matches none of `names`,
/// or `None` when every non-empty part matches at least one.
pub fn filter_error(filter: &str, names: &[String], noun: &str) -> Option<String> {
    let missing: Vec<&str> = parts(filter)
        .filter(|part| !names.iter().any(|name| name.contains(part)))
        .collect();
    if missing.is_empty() {
        return None;
    }
    let suggestion = |part: &str| {
        let nearest = nearest_names(part, names);
        if nearest.is_empty() {
            String::new()
        } else {
            format!(" (did you mean {}?)", quoted(&nearest))
        }
    };
    let what = match missing.as_slice() {
        [part] if filter.trim() == *part => {
            format!("EXAMPLES={filter} matches no example{}", suggestion(part))
        }
        [part] => format!(
            "EXAMPLES={filter} has a part that matches no example: `{part}`{}",
            suggestion(part)
        ),
        parts => {
            let clauses: Vec<String> = parts
                .iter()
                .map(|part| format!("`{part}`{}", suggestion(part)))
                .collect();
            format!(
                "EXAMPLES={filter} has parts that match no example: {}",
                clauses.join(", ")
            )
        }
    };
    Some(format!("{what}; EXAMPLES filters by {noun}"))
}

/// The `limit` `names` closest to `part`, nearest first.
fn nearest_names<'a>(part: &str, names: &'a [String]) -> Vec<&'a str> {
    let mut ranked: Vec<(&str, usize)> = names
        .iter()
        .map(|name| (name.as_str(), distance(part, name)))
        .collect();
    ranked.sort_by(|a, b| a.1.cmp(&b.1).then_with(|| a.0.cmp(b.0)));
    ranked.into_iter().map(|(name, _)| name).take(3).collect()
}

/// The edit distance between `a` and `b`, in characters.
fn distance(a: &str, b: &str) -> usize {
    let a: Vec<char> = a.chars().collect();
    let b: Vec<char> = b.chars().collect();
    let mut previous: Vec<usize> = (0..=b.len()).collect();
    let mut current = vec![0; b.len() + 1];
    for (i, ca) in a.iter().enumerate() {
        current[0] = i + 1;
        for (j, cb) in b.iter().enumerate() {
            let substitution = previous[j] + usize::from(ca != cb);
            current[j + 1] = (previous[j + 1] + 1).min(current[j] + 1).min(substitution);
        }
        std::mem::swap(&mut previous, &mut current);
    }
    previous[b.len()]
}

/// `` `a`, `b` or `c` ``, for a message.
fn quoted(names: &[&str]) -> String {
    match names {
        [] => String::new(),
        [only] => format!("`{only}`"),
        [first, second] => format!("`{first}` or `{second}`"),
        _ => {
            let (last, rest) = names.split_last().unwrap();
            let rest: Vec<String> = rest.iter().map(|name| format!("`{name}`")).collect();
            format!("{} or `{last}`", rest.join(", "))
        }
    }
}
