//! A missing standard library is a setup error the command reports, not a
//! panic (SW-1142).

use std::path::Path;
use std::process::{Command, Output, Stdio};

/// Runs `stitchwort` with `STITCHWORT_STD_DIR` naming `dir`.
fn stitchwort_with_std_dir(dir: &str, args: &[&str]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_stitchwort"))
        .args(args)
        .env("STITCHWORT_STD_DIR", dir)
        .stdin(Stdio::null())
        .output()
        .expect("run stitchwort")
}

/// `STITCHWORT_STD_DIR` naming a directory that doesn't exist: one clear
/// error saying what was looked for and how to point at a copy, exit 2, and
/// no panic text or backtrace note.
#[test]
fn a_missing_std_dir_is_a_clean_error() {
    let missing = "/nonexistent/stitchwort-std-for-test";
    let example = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../examples/accept/abort.sw");
    let output = stitchwort_with_std_dir(
        missing,
        &["check", &example.display().to_string(), "--no-cache"],
    );
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(output.status.code(), Some(2), "stderr:\n{stderr}");
    assert!(
        stderr.contains("the standard library at"),
        "stderr:\n{stderr}"
    );
    assert!(stderr.contains(missing), "stderr:\n{stderr}");
    assert!(stderr.contains("--std-dir"), "stderr:\n{stderr}");
    assert!(stderr.contains("STITCHWORT_STD_DIR"), "stderr:\n{stderr}");
    assert!(!stderr.contains("panicked"), "stderr:\n{stderr}");
    assert!(!stderr.contains("RUST_BACKTRACE"), "stderr:\n{stderr}");
}

/// `test --std Nat/Iterate.sw` runs the tests declared in that file and no
/// others, and a target that names no library file fails.
#[test]
fn test_std_runs_one_library_namespace_s_tests() {
    let run = |args: &[&str]| {
        let mut all = vec!["test", "--std"];
        all.extend_from_slice(args);
        Command::new(env!("CARGO_BIN_EXE_stitchwort"))
            .args(all)
            .stdin(Stdio::null())
            .output()
            .expect("run stitchwort")
    };
    let output = run(&["Nat/Iterate.sw"]);
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(output.status.success(), "stdout:\n{stdout}");
    assert!(stdout.contains("Nat.iterate dot"), "stdout:\n{stdout}");
    assert!(stdout.contains("2 test(s): 2 passed"), "stdout:\n{stdout}");
    assert!(!stdout.contains("divSuccStep"), "stdout:\n{stdout}");

    let output = run(&["Nope"]);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(output.status.code(), Some(1), "stderr:\n{stderr}");
    assert!(stderr.contains("E-STD-TARGET"), "stderr:\n{stderr}");
}

/// Copies the directory `from` to `to`, recursively.
fn copy_tree(from: &Path, to: &Path) {
    std::fs::create_dir_all(to).unwrap();
    for entry in std::fs::read_dir(from).unwrap().flatten() {
        let (source, target) = (entry.path(), to.join(entry.file_name()));
        if source.is_dir() {
            copy_tree(&source, &target);
        } else {
            std::fs::copy(&source, &target).unwrap();
        }
    }
}

/// The library's name index is read from the cache directory only for the
/// library it was made from (SW-4812): a name added to a file of a
/// `--std-dir` copy resolves on the next check, and is gone again once the
/// edit is undone, which finds the first index again.
#[test]
fn editing_a_std_dir_file_misses_the_cached_name_index() {
    let nanos = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map_or(0, |d| d.as_nanos());
    let scratch = std::env::temp_dir().join(format!(
        "stitchwort-index-std-dir-{}-{nanos}",
        std::process::id()
    ));
    let std = scratch.join("std");
    copy_tree(
        &Path::new(env!("CARGO_MANIFEST_DIR")).join("../elab/src/std"),
        &std,
    );
    let program = scratch.join("probe.sw");
    std::fs::write(
        &program,
        "import Std (Nat)\ndef probe: Nat := Nat.indexCacheProbe 3\n",
    )
    .unwrap();
    let cache = scratch.join("cache");
    let check = || {
        let output = Command::new(env!("CARGO_BIN_EXE_stitchwort"))
            .args(["--std-dir", &std.display().to_string(), "check"])
            .arg(&program)
            .arg("--cache-dir")
            .arg(&cache)
            .stdin(Stdio::null())
            .output()
            .expect("run stitchwort");
        let text = String::from_utf8_lossy(&output.stdout).to_string()
            + &String::from_utf8_lossy(&output.stderr);
        (output.status.success(), text)
    };
    let indexes = || std::fs::read_dir(cache.join("std-index")).map_or(0, |d| d.count());

    let file = std.join("Nat/Iterate.sw");
    let original = std::fs::read_to_string(&file).unwrap();
    let (ok, text) = check();
    assert!(!ok, "no such name yet:\n{text}");
    assert!(text.contains("indexCacheProbe"), "{text}");
    assert_eq!(indexes(), 1, "the index is written");

    std::fs::write(
        &file,
        format!("{original}\ndef Nat.indexCacheProbe (n: Nat): Nat := n\n"),
    )
    .unwrap();
    let (ok, text) = check();
    assert!(ok, "the added name resolves:\n{text}");
    assert_eq!(indexes(), 2, "the edited library has an index of its own");

    std::fs::write(&file, &original).unwrap();
    let (ok, text) = check();
    assert!(!ok, "the name is gone again:\n{text}");
    assert_eq!(indexes(), 2, "the first index is found again");
    let _ = std::fs::remove_dir_all(&scratch);
}

/// A scratch folder for one test, removed by the test at its end.
fn scratch_dir(name: &str) -> std::path::PathBuf {
    let nanos = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map_or(0, |d| d.as_nanos());
    let dir =
        std::env::temp_dir().join(format!("stitchwort-{name}-{}-{nanos}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    dir
}

/// Runs `stitchwort` in `cwd` with `args`; whether it succeeded and what it
/// said.
fn stitchwort_in(cwd: &Path, args: &[&str]) -> (bool, String) {
    let output = Command::new(env!("CARGO_BIN_EXE_stitchwort"))
        .args(args)
        .current_dir(cwd)
        .stdin(Stdio::null())
        .output()
        .expect("run stitchwort");
    let text = String::from_utf8_lossy(&output.stdout).to_string()
        + &String::from_utf8_lossy(&output.stderr);
    (output.status.success(), text)
}

/// How many library indexes the cache folder `cache` holds.
fn indexes_in(cache: &Path) -> usize {
    std::fs::read_dir(cache.join("std-index")).map_or(0, |d| d.count())
}

/// `run` and `test` of a file read and write the library's name index in
/// `--cache-dir` as `check` does (SW-4821), and write none with `--no-cache`.
#[test]
fn run_and_test_of_a_file_use_the_name_index_cache() {
    let scratch = scratch_dir("index-run-test");
    let file = scratch.join("probe.sw");
    std::fs::write(
        &file,
        "def main(): {IO} () := IO.print \"hi\"\ntest \"one\" := 1 + 1 = 2\n",
    )
    .unwrap();
    let file = file.display().to_string();
    for command in ["run", "test"] {
        let cache = scratch.join(format!("cache-{command}"));
        let cache_arg = cache.display().to_string();
        let (ok, text) = stitchwort_in(&scratch, &[command, &file, "--cache-dir", &cache_arg]);
        assert!(ok, "{command}:\n{text}");
        assert_eq!(indexes_in(&cache), 1, "{command} writes the index");
        let (ok, text) = stitchwort_in(&scratch, &[command, &file, "--cache-dir", &cache_arg]);
        assert!(ok, "{command} again:\n{text}");
        assert_eq!(indexes_in(&cache), 1, "{command} finds it again");

        let off = scratch.join(format!("off-{command}"));
        let off_arg = off.display().to_string();
        let (ok, text) = stitchwort_in(&scratch, &[command, &file, "--no-cache"]);
        assert!(ok, "{command} --no-cache:\n{text}");
        assert!(
            !scratch.join(".stitchwort").exists() && !off.exists(),
            "{command} --no-cache leaves no cache ({off_arg})"
        );
    }
    let _ = std::fs::remove_dir_all(&scratch);
}

/// `run` and `test` of a project use the project's `.stitchwort/cache`.
#[test]
fn run_and_test_of_a_project_use_the_name_index_cache() {
    let scratch = scratch_dir("index-project");
    std::fs::write(scratch.join("stitchwort.yaml"), "sources: [src]\n").unwrap();
    std::fs::create_dir_all(scratch.join("src/Probe")).unwrap();
    std::fs::write(
        scratch.join("src/Probe/Main.sw"),
        "namespace Probe.Main\n\ndef main(): {IO} () := IO.print \"hi\"\n\ntest \"one\" := 1 + 1 = 2\n",
    )
    .unwrap();
    let cache = scratch.join(".stitchwort/cache");
    let (ok, text) = stitchwort_in(&scratch, &["run", "Probe.Main.main"]);
    assert!(ok, "run:\n{text}");
    assert_eq!(indexes_in(&cache), 1, "run writes the index");
    std::fs::remove_dir_all(cache.join("std-index")).unwrap();
    let (ok, text) = stitchwort_in(&scratch, &["test", "Probe.Main"]);
    assert!(ok, "test:\n{text}");
    assert_eq!(indexes_in(&cache), 1, "test writes the index");
    let _ = std::fs::remove_dir_all(&scratch);
}

/// `search` in a project starts its session from the project's cache, as
/// `check` does (SW-4935): it writes the library's name index there before
/// it reads the project. The project's namespaces clash, so the search
/// stops at that error, without loading the library.
#[test]
fn search_in_a_project_uses_the_name_index_cache() {
    let scratch = scratch_dir("index-search");
    std::fs::write(scratch.join("stitchwort.yaml"), "sources: [src]\n").unwrap();
    std::fs::create_dir_all(scratch.join("src/P")).unwrap();
    std::fs::write(scratch.join("src/P.sw"), "namespace P\n\ndef Q: Nat := 1\n").unwrap();
    std::fs::write(
        scratch.join("src/P/Q.sw"),
        "namespace P.Q\n\ndef x: Nat := 1\n",
    )
    .unwrap();
    let (ok, text) = stitchwort_in(&scratch, &["search", "Nat"]);
    assert!(!ok && text.contains("E-NAMESPACE-CLASH"), "search:\n{text}");
    assert_eq!(
        indexes_in(&scratch.join(".stitchwort/cache")),
        1,
        "search writes the index"
    );
    let _ = std::fs::remove_dir_all(&scratch);
}

/// An edited `--std-dir` copy gets an index of its own under `run`, as under
/// `check`: the cache is keyed by the library's text.
#[test]
fn run_with_an_edited_std_dir_gets_its_own_index() {
    let scratch = scratch_dir("index-run-std-dir");
    let std = scratch.join("std");
    copy_tree(
        &Path::new(env!("CARGO_MANIFEST_DIR")).join("../elab/src/std"),
        &std,
    );
    let program = scratch.join("probe.sw");
    std::fs::write(
        &program,
        "import Std (Nat)\ndef main(): {IO} () := IO.print \"hi\"\ndef probe: Nat := Nat.indexCacheProbe 3\n",
    )
    .unwrap();
    let (cache, std_arg, program_arg) = (
        scratch.join("cache"),
        std.display().to_string(),
        program.display().to_string(),
    );
    let cache_arg = cache.display().to_string();
    let run = || {
        stitchwort_in(
            &scratch,
            &[
                "--std-dir",
                &std_arg,
                "run",
                &program_arg,
                "--cache-dir",
                &cache_arg,
            ],
        )
    };
    let (ok, text) = run();
    assert!(
        !ok && text.contains("indexCacheProbe"),
        "no such name yet:\n{text}"
    );
    assert_eq!(indexes_in(&cache), 1);
    let file = std.join("Nat/Iterate.sw");
    let original = std::fs::read_to_string(&file).unwrap();
    std::fs::write(
        &file,
        format!("{original}\ndef Nat.indexCacheProbe (n: Nat): Nat := n\n"),
    )
    .unwrap();
    let (ok, text) = run();
    assert!(ok, "the added name resolves:\n{text}");
    assert_eq!(
        indexes_in(&cache),
        2,
        "the edited library has its own index"
    );
    let _ = std::fs::remove_dir_all(&scratch);
}

/// Sends `message` to a language server's input, framed.
fn lsp_send(input: &mut impl std::io::Write, message: &serde_json::Value) {
    let body = message.to_string();
    write!(input, "Content-Length: {}\r\n\r\n{body}", body.len()).unwrap();
    input.flush().unwrap();
}

/// The language server reads the library's name index from the first
/// workspace folder's cache folder when it has one (SW-4821), and doesn't
/// make a cache folder where there is none.
#[test]
fn the_language_server_uses_the_name_index_cache_of_its_workspace() {
    use serde_json::json;
    let scratch = scratch_dir("index-lsp");
    let cache = scratch.join(".stitchwort/cache");
    std::fs::create_dir_all(&cache).unwrap();
    let file = scratch.join("probe.sw");
    let text = "def one: Nat := 1\n";
    std::fs::write(&file, text).unwrap();
    let mut child = Command::new(env!("CARGO_BIN_EXE_stitchwort"))
        .arg("lsp")
        .current_dir(std::env::temp_dir())
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::null())
        .spawn()
        .expect("start the server");
    let mut input = child.stdin.take().unwrap();
    let root = format!("file://{}", scratch.display());
    lsp_send(
        &mut input,
        &json!({"jsonrpc": "2.0", "id": 1, "method": "initialize", "params": {
            "capabilities": {}, "workspaceFolders": [{"uri": root, "name": "probe"}]}}),
    );
    lsp_send(
        &mut input,
        &json!({"jsonrpc": "2.0", "method": "initialized", "params": {}}),
    );
    lsp_send(
        &mut input,
        &json!({"jsonrpc": "2.0", "method": "textDocument/didOpen", "params": {"textDocument": {
            "uri": format!("{root}/probe.sw"), "languageId": "stitchwort", "version": 1, "text": text}}}),
    );
    // The first answers to the file are its diagnostics, which need a
    // session; the index is made by then.
    let mut output = std::io::BufReader::new(child.stdout.take().unwrap());
    let mut seen = String::new();
    loop {
        use std::io::{BufRead, Read};
        let mut length = None;
        loop {
            let mut line = String::new();
            if output.read_line(&mut line).unwrap() == 0 {
                panic!("the server stopped early:\n{seen}");
            }
            if line.trim().is_empty() {
                break;
            }
            if let Some(n) = line.trim().strip_prefix("Content-Length: ") {
                length = n.parse::<usize>().ok();
            }
        }
        let mut body = vec![0; length.expect("a length")];
        output.read_exact(&mut body).unwrap();
        let body = String::from_utf8_lossy(&body).to_string();
        seen.push_str(&body);
        if body.contains("publishDiagnostics") {
            break;
        }
    }
    lsp_send(
        &mut input,
        &json!({"jsonrpc": "2.0", "id": 2, "method": "shutdown"}),
    );
    lsp_send(&mut input, &json!({"jsonrpc": "2.0", "method": "exit"}));
    drop(input);
    let _ = child.wait();
    assert_eq!(indexes_in(&cache), 1, "the server wrote the index");
    let _ = std::fs::remove_dir_all(&scratch);
}
