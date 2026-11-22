//! `stitchwort build`: standalone executables (stages S3 and S5 of
//! docs/proposals/standalone-executables.md). A built executable must do
//! exactly what `stitchwort run` does: the same output, errors and exit
//! statuses, and the terminal put back however it ends.
//!
//! The executables link the runtime library the test build made
//! (`libstitchwort_standalone.a`, built because this package depends on
//! `stitchwort-standalone`), found beside the test binary; one left from an
//! older build is skipped; `STITCHWORT_RUNTIME` overrides that. Each test needs a C compiler to link
//! with (`$CC`, or `cc`), and is skipped with a note without one.
//!
//! The roguelike's tests (with and without `--native`) each check the whole
//! game twice (about 2 s), so they're left out of the lane tier
//! (`.config/nextest.toml`); the rest are quick.
//! The `--native` tests need a `stitchwort` with the `native` feature, which
//! the test tiers build.

use std::ffi::OsStr;
use std::path::{Path, PathBuf};
use std::process::{Command, Output, Stdio};

#[cfg(unix)]
use crate::pty;

/// The runtime library to link with: `STITCHWORT_RUNTIME`, or the newest
/// `libstitchwort_standalone*.a` beside this test binary (in `deps/`) built
/// from the runtime sources this build has.
fn runtime_library() -> PathBuf {
    if let Some(path) = std::env::var_os("STITCHWORT_RUNTIME") {
        return path.into();
    }
    let exe = std::env::current_exe().expect("the test binary's path");
    let dir = exe.parent().expect("the test binary's folder");
    std::fs::read_dir(dir)
        .expect("read the test binary's folder")
        .filter_map(Result::ok)
        .filter(|entry| {
            let name = entry.file_name();
            let name = name.to_string_lossy();
            name.starts_with("libstitchwort_standalone") && name.ends_with(".a")
        })
        .filter(|entry| holds_marker(&entry.path()))
        .max_by_key(|entry| entry.metadata().and_then(|m| m.modified()).ok())
        .map(|entry| entry.path())
        .unwrap_or_else(|| {
            panic!(
                "no libstitchwort_standalone*.a in {}: the dev-dependency on \
                 stitchwort-standalone should have built it",
                dir.display()
            )
        })
}

/// Whether the library at `path` holds this build's runtime marker.
fn holds_marker(path: &Path) -> bool {
    let marker = stitchwort_rt::BUILD_MARKER.as_bytes();
    std::fs::read(path).is_ok_and(|bytes| bytes.windows(marker.len()).any(|w| w == marker))
}

/// Whether there's a C compiler to link with; if not, says the test is
/// skipped.
fn have_cc() -> bool {
    let cc = std::env::var_os("CC")
        .filter(|cc| !cc.is_empty())
        .unwrap_or_else(|| "cc".into());
    let found = Command::new(&cc)
        .arg("--version")
        .stdout(Stdio::null())
        .stderr(Stdio::null())
        .status()
        .is_ok();
    if !found {
        eprintln!("skipped: no C compiler (`{}`)", cc.to_string_lossy());
    }
    found
}

/// The check cache every test here shares: the library replays from it
/// instead of being checked from source by each build and run (about 10 s of
/// CPU each). Keys hold the sources by content, so sharing is safe; the
/// first writers fill it, concurrently, which the cache allows.
const CACHE: &str = concat!(env!("CARGO_TARGET_TMPDIR"), "/build-tests-cache");

/// A fresh folder for one test.
fn work_dir(name: &str) -> PathBuf {
    let dir = Path::new(env!("CARGO_TARGET_TMPDIR"))
        .join("build-tests")
        .join(name);
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("make the test's folder");
    dir
}

/// `stitchwort ARGS` in `dir`, linking with the test build's library.
fn stitchwort(dir: &Path, args: &[&str], input: &[u8]) -> Output {
    stitchwort_with_env(dir, args, input, &[])
}

/// [`stitchwort`] with more environment variables set.
fn stitchwort_with_env(dir: &Path, args: &[&str], input: &[u8], env: &[(&str, &str)]) -> Output {
    let mut command = match args.split_first() {
        Some((subcommand, flags)) => crate::common::cli_with(subcommand, flags),
        None => crate::common::cli_plain("--help"),
    };
    command
        .current_dir(dir)
        .env("STITCHWORT_RUNTIME", runtime_library())
        .envs(env.iter().copied());
    run_with_input(command, input)
}

fn run_with_input(mut command: Command, input: &[u8]) -> Output {
    use std::io::Write;
    let mut child = command
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("start the command");
    // A program may end before reading it all.
    let _ = child.stdin.take().expect("stdin").write_all(input);
    child.wait_with_output().expect("wait for the command")
}

fn text(bytes: &[u8]) -> String {
    String::from_utf8_lossy(bytes).into_owned()
}

/// Builds `args` (a target and options) in `dir`, which must succeed.
fn build(dir: &Path, args: &[&str]) {
    let mut all = vec!["build"];
    all.extend_from_slice(args);
    let output = stitchwort(dir, &all, b"");
    assert!(
        output.status.success(),
        "build failed: {}",
        text(&output.stderr)
    );
    // The linker said nothing: no warnings.
    assert_eq!(text(&output.stderr), "");
}

/// The executable `exe` on `input`, in its own folder, where `stitchwort`
/// runs too.
fn run_executable(exe: &Path, input: &[u8]) -> Output {
    let mut command = Command::new(exe);
    command.current_dir(exe.parent().expect("in a folder"));
    run_with_input(command, input)
}

/// Writes `source` as `name` in `dir`, builds it, and checks that the
/// executable's output, errors and exit status on each of `inputs` are
/// `stitchwort run`'s. Returns the executable and what it did on the first
/// input.
fn same_as_run(dir: &Path, name: &str, source: &str, inputs: &[&[u8]]) -> (PathBuf, Output) {
    std::fs::write(dir.join(name), source).expect("write the source");
    build(dir, &[name, "--cache-dir", CACHE, "-o", "program"]);
    let exe = dir.join("program");
    let mut first = None;
    for input in inputs {
        let ran = stitchwort(dir, &["run", "--cache-dir", CACHE, name], input);
        let built = run_executable(&exe, input);
        assert_eq!(text(&built.stdout), text(&ran.stdout), "standard output");
        assert_eq!(text(&built.stderr), text(&ran.stderr), "standard error");
        assert_eq!(built.status.code(), ran.status.code(), "exit status");
        first.get_or_insert(built);
    }
    (exe, first.expect("at least one input"))
}

/// Reads lines until the end, then all that's left is nothing: `readLine`,
/// `readAll` and `print`, as `run` does them.
const ECHO: &str = r#"import Std (IO, Nat, Text)

def echoLine: Option Text → (() → {IO, Partial | e} ()) → {IO, Partial | e} ()
  | None, more =>
    let rest := IO.readAll()
    IO.print "done, ${Nat.toText (Text.length rest)} left"
  | Some l, more =>
    IO.print "got ${l}"
    more()

def echo(): {IO, Partial} () := echoLine (IO.readLine()) echo

def main(): {IO, Partial} () := echo()
"#;

#[test]
fn an_io_program_runs_as_it_does_under_run() {
    if !have_cc() {
        return;
    }
    let dir = work_dir("io");
    let (_, first) = same_as_run(
        &dir,
        "echo.sw",
        ECHO,
        &[b"one\ntwo\r\nthree", b"", b"bad \xff\n"],
    );
    assert_eq!(
        text(&first.stdout),
        "got one\ngot two\ngot three\ndone, 0 left\n"
    );
    assert_eq!(first.status.code(), Some(0));
}

/// A `main` with `Files` performs it in a built executable as under `run`,
/// on the folder it is started in; `IO.printError` writes to standard error.
#[test]
fn a_files_program_runs_as_it_does_under_run() {
    if !have_cc() {
        return;
    }
    let dir = work_dir("files");
    let source = r#"import Std (FileError, Files, IO, Path, Result, Text)

def say (result: Result Text FileError): {IO} () := match result with
  | Ok text => IO.print text
  | Err error => IO.printError "${error}"

def main(): {Files, IO} () :=
  Files.write ("out.txt".toPath, "written é")
  say (Files.read "out.txt".toPath)
  say (Files.read "missing.txt".toPath)
"#;
    let (_, first) = same_as_run(&dir, "files.sw", source, &[b""]);
    assert_eq!(text(&first.stdout), "written é\n");
    assert_eq!(text(&first.stderr), "missing.txt: no such file or folder\n");
    // The executable writes in the folder it is started in.
    std::fs::remove_file(dir.join("out.txt")).expect("the runs wrote it");
    run_executable(&dir.join("program"), b"");
    assert_eq!(
        std::fs::read_to_string(dir.join("out.txt")).expect("the executable wrote it"),
        "written é"
    );
}

/// A `main` returning an `ExitStatus`: a built executable exits with it, as
/// `run` does.
#[test]
fn a_main_returning_an_exit_status_exits_with_it_in_a_built_executable() {
    if !have_cc() {
        return;
    }
    let dir = work_dir("exit-status");
    let source = include_str!("../../../../examples/accept/main-exit-status.sw");
    let inputs: [&[u8]; 3] = [b"", b"ok\n", b"no\n"];
    let (exe, first) = same_as_run(&dir, "status.sw", source, &inputs);
    assert_eq!(first.status.code(), Some(3));
    assert_eq!(run_executable(&exe, b"ok\n").status.code(), Some(0));
    assert_eq!(run_executable(&exe, b"no\n").status.code(), Some(1));
}

/// The same with `--native`: the executable, `run --native` and `run` agree.
#[cfg(feature = "native")]
#[test]
fn a_main_returning_an_exit_status_exits_with_it_in_native_code() {
    if !have_cc() {
        return;
    }
    let dir = work_dir("exit-status-native");
    let source = include_str!("../../../../examples/accept/main-exit-status.sw");
    let (_, built) = native_same_as_run(&dir, "status.sw", source, b"");
    assert_eq!(text(&built.stdout), "checking\n");
    assert_eq!(built.status.code(), Some(3));
}

/// `IO`, `Fail`, `Files` and `Partial` together, in a built executable as
/// under `run`.
#[test]
fn a_main_with_every_ability_runs_as_it_does_under_run() {
    if !have_cc() {
        return;
    }
    let dir = work_dir("every-ability");
    let (_, first) = same_as_run(&dir, "every.sw", crate::files::EVERY_ABILITY, &[b""]);
    assert_eq!(first.status.code(), Some(1));
    assert_eq!(text(&first.stderr), "counting\nerror: lift-off failed\n");
}

/// `IO.args` gives an executable's arguments after its name, as `run` gives
/// those after `--`.
#[test]
fn an_executable_gets_its_arguments() {
    if !have_cc() {
        return;
    }
    let dir = work_dir("args");
    std::fs::write(
        dir.join("args.sw"),
        "import Std (IO, List, Text)\ndef main () : {IO} () := IO.print (Text.joinWith (IO.args ()) \"|\")\n",
    )
    .expect("write the source");
    build(&dir, &["args.sw", "--cache-dir", CACHE, "-o", "program"]);
    let built = run_with_input(
        {
            let mut command = Command::new(dir.join("program"));
            command.args(["1", "two words"]);
            command
        },
        b"",
    );
    assert_eq!(text(&built.stdout), "1|two words\n");
    let ran = stitchwort(
        &dir,
        &[
            "run",
            "--cache-dir",
            CACHE,
            "args.sw",
            "--",
            "1",
            "two words",
        ],
        b"",
    );
    assert_eq!(text(&ran.stdout), text(&built.stdout));
}

/// The executable is named after the file by default, and signed on macOS,
/// where an unsigned one would be killed (§7.2).
#[test]
fn the_executable_is_named_after_its_file_and_signed() {
    if !have_cc() {
        return;
    }
    let dir = work_dir("named");
    std::fs::write(dir.join("echo.sw"), ECHO).expect("write the source");
    build(&dir, &["echo.sw", "--cache-dir", CACHE]);
    let exe = dir.join("echo");
    assert_eq!(
        text(&run_executable(&exe, b"x\n").stdout),
        "got x\ndone, 0 left\n"
    );
    if cfg!(target_os = "macos") {
        match Command::new("codesign").arg("-v").arg(&exe).output() {
            Ok(verified) => assert!(verified.status.success(), "{}", text(&verified.stderr)),
            // A build sandbox without Apple's tools.
            Err(e) => eprintln!("skipped the signature check: no codesign ({e})"),
        }
    }
}

/// On macOS, the executable `exe` links only libraries under `/usr/lib` and
/// `/System`, never ones from the Nix store.
fn assert_system_libraries_only(exe: &Path) {
    if !cfg!(target_os = "macos") {
        return;
    }
    let listed = match Command::new("otool").arg("-L").arg(exe).output() {
        Ok(listed) => listed,
        Err(e) => {
            eprintln!("skipped the library check: no otool ({e})");
            return;
        }
    };
    let listed = text(&listed.stdout);
    let libraries: Vec<&str> = listed
        .lines()
        .skip(1)
        .filter_map(|line| line.split_whitespace().next())
        .collect();
    assert!(!libraries.is_empty(), "otool -L listed nothing: {listed}");
    for library in libraries {
        assert!(
            library.starts_with("/usr/lib/") || library.starts_with("/System/"),
            "{library} is not a system library: {listed}"
        );
    }
}

/// On Linux an executable, with native code or without, is static: its
/// ELF headers name no interpreter (`PT_INTERP`) and no shared library
/// (`DT_NEEDED`), so it runs on any Linux of its architecture.
#[cfg(target_os = "linux")]
#[test]
fn the_executable_is_static_on_linux() {
    use object::elf::{DT_NEEDED, FileHeader64, PT_INTERP};
    use object::read::elf::{Dyn as _, FileHeader as _, ProgramHeader as _};
    if !have_cc() {
        return;
    }
    let dir = work_dir("static");
    std::fs::write(dir.join("echo.sw"), ECHO).expect("write the source");
    let mut builds = vec![vec!["echo.sw", "-o", "machine"]];
    if cfg!(feature = "native") {
        builds.push(vec!["echo.sw", "--native", "-o", "native"]);
    }
    for args in builds {
        build(&dir, &args);
        let exe = dir.join(args[args.len() - 1]);
        let data = std::fs::read(&exe).expect("read the executable");
        let header = FileHeader64::<object::Endianness>::parse(&*data).expect("an ELF file");
        let endian = header.endian().expect("its byte order");
        for segment in header
            .program_headers(endian, &*data)
            .expect("its program headers")
        {
            assert_ne!(segment.p_type(endian), PT_INTERP, "{}", exe.display());
            if let Some(entries) = segment.dynamic(endian, &*data).expect("its dynamic table") {
                assert!(
                    entries.iter().all(|entry| entry.tag(endian) != DT_NEEDED),
                    "{} needs a shared library",
                    exe.display()
                );
            }
        }
        assert_eq!(
            text(&run_executable(&exe, b"x\n").stdout),
            "got x\ndone, 0 left\n"
        );
    }
}

#[test]
fn the_executable_links_only_system_libraries() {
    if !have_cc() {
        return;
    }
    let dir = work_dir("system-libs");
    std::fs::write(dir.join("echo.sw"), ECHO).expect("write the source");
    build(&dir, &["echo.sw", "--cache-dir", CACHE]);
    assert_system_libraries_only(&dir.join("echo"));
}

#[cfg(feature = "native")]
#[test]
fn the_native_executable_links_only_system_libraries() {
    if !have_cc() {
        return;
    }
    let dir = work_dir("system-libs-native");
    std::fs::write(dir.join("echo.sw"), ECHO).expect("write the source");
    build(&dir, &["echo.sw", "--native", "--cache-dir", CACHE]);
    assert_system_libraries_only(&dir.join("echo"));
}

/// An unhandled `Fail`: what was printed, then `error: <msg>`, and status 1.
#[test]
fn a_failing_program_fails_as_it_does_under_run() {
    if !have_cc() {
        return;
    }
    let dir = work_dir("fail");
    let (_, first) = same_as_run(
        &dir,
        "fail.sw",
        include_str!("../../../../examples/accept/main-fail.sw"),
        &[b""],
    );
    assert_eq!(first.status.code(), Some(1));
    assert_eq!(text(&first.stdout), "reading the numbers\n");
    assert!(
        text(&first.stderr).starts_with("error: "),
        "{}",
        text(&first.stderr)
    );
}

/// Recursion past the frame limit: `E-RESOURCE`, as `run` reports it but for
/// the excerpt of `main`'s source, which the executable doesn't have, and
/// status 2.
#[test]
fn a_program_out_of_frames_reports_as_run_does() {
    if !have_cc() {
        return;
    }
    let dir = work_dir("frames");
    let source = "import Std (Nat)\n\n\
                  def count : Nat -> Nat\n  \
                    | 0      => 0\n  \
                    | Succ n => 2 * count n\n\n\
                  def main () : {IO} () :=\n  \
                    IO.print \"before\"\n  \
                    IO.print (Nat.toText (count (5 * 1000 * 1000)))\n";
    std::fs::write(dir.join("runaway.sw"), source).expect("write the source");
    build(&dir, &["runaway.sw", "--cache-dir", CACHE]);
    let built = run_executable(&dir.join("runaway"), b"");
    let ran = stitchwort(&dir, &["run", "--cache-dir", CACHE, "runaway.sw"], b"");
    assert_eq!(built.status.code(), Some(2));
    assert_eq!(ran.status.code(), Some(2));
    assert_eq!(text(&built.stdout), "before\n");
    assert_eq!(text(&built.stdout), text(&ran.stdout));
    let stderr = text(&built.stderr);
    let mut lines = stderr.lines();
    let first = lines.next().unwrap_or_default();
    assert!(
        first.starts_with("[E-RESOURCE] Error: ran out of resources: "),
        "{stderr}"
    );
    // The same message and notes as `run`'s report.
    let message = first.trim_start_matches("[E-RESOURCE] Error: ");
    let ran_stderr = text(&ran.stderr);
    assert!(ran_stderr.contains(message), "{ran_stderr}");
    let notes: Vec<&str> = lines.collect();
    assert!(
        notes.iter().any(
            |note| note.starts_with("  note: the recursion was deepest in")
                && note.contains("count")
        ),
        "{stderr}"
    );
    for note in notes {
        let note = note.trim_start_matches("  note: ");
        assert!(ran_stderr.contains(note), "{note:?} isn't in {ran_stderr}");
    }
}

/// `build` says what's wrong when it can't link: no library, no C compiler,
/// or a linker that fails, with what the linker said.
#[test]
fn link_failures_are_explained() {
    let dir = work_dir("link-errors");
    std::fs::write(dir.join("echo.sw"), ECHO).expect("write the source");
    let build_with = |variable: &str, value: &OsStr| {
        let mut command = Command::new(env!("CARGO_BIN_EXE_stitchwort"));
        command
            .args(["build", "echo.sw", "--cache-dir", CACHE])
            .current_dir(&dir)
            .env("STITCHWORT_RUNTIME", runtime_library())
            .env(variable, value);
        run_with_input(command, b"")
    };

    let missing = build_with(
        "STITCHWORT_RUNTIME",
        OsStr::new("/no/such/libstitchwort_standalone.a"),
    );
    assert_eq!(missing.status.code(), Some(1));
    assert_eq!(
        text(&missing.stderr),
        "error: there's no runtime library at /no/such/libstitchwort_standalone.a, which \
         STITCHWORT_RUNTIME names\n"
    );

    let no_cc = build_with("CC", OsStr::new("/no/such/cc"));
    assert_eq!(no_cc.status.code(), Some(1));
    let stderr = text(&no_cc.stderr);
    assert!(
        stderr.starts_with(
            "error: can't find a C compiler to link with: there's no `/no/such/cc` on the PATH\n"
        ),
        "{stderr}"
    );
    assert!(
        stderr.contains("  note: `build` links the executable"),
        "{stderr}"
    );

    if !have_cc() {
        return;
    }
    let bogus = dir.join("libbogus.a");
    std::fs::write(
        &bogus,
        format!("not an archive {}", stitchwort_rt::BUILD_MARKER),
    )
    .expect("write the bogus library");
    let failed = build_with("STITCHWORT_RUNTIME", bogus.as_os_str());
    assert_eq!(failed.status.code(), Some(1));
    let stderr = text(&failed.stderr);
    // `$CC`, or `cc`.
    assert!(
        stderr.starts_with("error: linking failed: `") && stderr.contains("` ended with "),
        "{stderr}"
    );
    // Then what the linker said, which names the file it couldn't use.
    assert!(
        stderr.lines().count() > 1 && stderr.contains("libbogus.a"),
        "{stderr}"
    );
    assert!(!dir.join("echo").exists());
}

/// A runtime library from another build of the runtime is refused with a
/// message that says what to do, instead of linking an executable that can't
/// read its own program (SW-3149).
#[test]
fn a_stale_runtime_library_is_refused() {
    let dir = work_dir("stale-library");
    std::fs::write(dir.join("echo.sw"), ECHO).expect("write the source");
    let stale = dir.join("libstale.a");
    std::fs::write(&stale, "stitchwort-runtime-build=1;").expect("write the library");
    let mut command = Command::new(env!("CARGO_BIN_EXE_stitchwort"));
    command
        .args(["build", "echo.sw", "--cache-dir", CACHE])
        .current_dir(&dir)
        .env("STITCHWORT_RUNTIME", &stale);
    let output = run_with_input(command, b"");
    assert_eq!(output.status.code(), Some(1));
    let stderr = text(&output.stderr);
    assert!(
        stderr.starts_with("error: the runtime library is from a different build"),
        "{stderr}"
    );
    assert!(stderr.contains("task build"), "{stderr}");
    assert!(!dir.join("echo").exists());
}

/// A project folder builds its one namespace with a `main`; one with none
/// says how to name the function instead.
#[test]
fn a_project_folder_builds_its_main() {
    if !have_cc() {
        return;
    }
    let dir = work_dir("project");
    let project = dir.join("greeter");
    std::fs::create_dir_all(project.join("src/Greet")).expect("make the project");
    std::fs::write(project.join("stitchwort.yaml"), "sources: [src]\n").expect("write");
    std::fs::write(
        project.join("src/Greet/Greet.sw"),
        "namespace Greet\nimport Std (IO)\n\ndef main(): {IO} () := IO.print \"hello\"\n",
    )
    .expect("write");
    std::fs::write(
        project.join("src/Greet/Words.sw"),
        "namespace Greet.Words\n\ndef word: Text := \"hi\"\n",
    )
    .expect("write");
    // Named after the folder by default, which is here already.
    let clash = stitchwort(&dir, &["build", "greeter"], b"");
    assert_eq!(clash.status.code(), Some(1));
    assert_eq!(
        text(&clash.stderr),
        "error: can't write the executable to greeter: it's a folder\n  note: name the \
         executable with -o\n"
    );
    build(&dir, &["greeter", "-o", "greeter-app"]);
    assert_eq!(
        text(&run_executable(&dir.join("greeter-app"), b"").stdout),
        "hello\n"
    );
    // A function of the project, by its full name: named after its
    // namespace.
    build(&project, &["Greet.main"]);
    assert_eq!(
        text(&run_executable(&project.join("greet"), b"").stdout),
        "hello\n"
    );

    std::fs::remove_file(project.join("src/Greet/Greet.sw")).expect("remove main");
    let output = stitchwort(&dir, &["build", "greeter"], b"");
    assert_eq!(output.status.code(), Some(1));
    assert_eq!(
        text(&output.stderr),
        "error: no namespace of project greeter/ declares `main`\n  note: name the function \
         to build, as in `stitchwort build Name.main --project greeter`\n"
    );
}

/// A project folder with two namespaces that declare `main` is not guessed
/// at: the error names both, and the note shows how to pick one.
#[test]
fn a_project_folder_with_two_mains_names_them() {
    let dir = work_dir("two-mains");
    let project = dir.join("pair");
    std::fs::create_dir_all(project.join("src")).expect("make the project");
    std::fs::write(project.join("stitchwort.yaml"), "sources: [src]\n").expect("write");
    for namespace in ["Fmt", "Timing"] {
        std::fs::write(
            project.join(format!("src/{namespace}.sw")),
            format!("namespace {namespace}\nimport Std (IO)\n\ndef main(): {{IO}} () := IO.print \"{namespace}\"\n"),
        )
        .expect("write");
    }
    let output = stitchwort(&dir, &["build", "pair"], b"");
    assert_eq!(output.status.code(), Some(1));
    assert_eq!(
        text(&output.stderr),
        "error: more than one namespace of project pair/ declares `main`: Fmt, Timing\n  note: \
         name the one to build, as in `stitchwort build Fmt.main --project pair`\n"
    );
}

/// A copy of the roguelike in `dir`, seeded with a constant instead of
/// `IO.randomSeed`, so that every run plays the same game.
fn seeded_rogue(dir: &Path) -> PathBuf {
    fn copy_tree(from: &Path, to: &Path) {
        std::fs::create_dir_all(to).expect("make a folder");
        for entry in std::fs::read_dir(from).expect("read a folder") {
            let entry = entry.expect("an entry");
            let target = to.join(entry.file_name());
            if entry.file_type().expect("its type").is_dir() {
                copy_tree(&entry.path(), &target);
            } else {
                std::fs::copy(entry.path(), &target).expect("copy a file");
            }
        }
    }
    let rogue = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../games/rogue");
    let copy = dir.join("rogue");
    copy_tree(&rogue.join("src"), &copy.join("src"));
    std::fs::copy(rogue.join("stitchwort.yaml"), copy.join("stitchwort.yaml")).expect("copy");
    let main = copy.join("src/Rogue/Rogue.sw");
    let source = std::fs::read_to_string(&main).expect("read Rogue.sw");
    let seeded = source.replace("IO.randomSeed() % 2147483648", "12345");
    assert_ne!(
        seeded, source,
        "Rogue.main no longer seeds itself as this test expects"
    );
    std::fs::write(&main, seeded).expect("write Rogue.sw");
    copy
}

/// Milestone M1: the roguelike, built from its folder, plays as `stitchwort
/// run Rogue.main` does on the same keys; and in a terminal, `q` quits it
/// with the terminal put back. Built without `--native`, it has the machine
/// (and the check below would find it), and no native code's runtime.
#[test]
fn the_roguelike_plays_as_it_does_under_run() {
    if !have_cc() {
        return;
    }
    let dir = work_dir("rogue");
    let project = seeded_rogue(&dir);
    build(&dir, &["rogue", "-o", "rogue-game"]);
    let exe = dir.join("rogue-game");
    let built = run_executable(&exe, b"jjlq");
    let ran = stitchwort(&project, &["run", "Rogue.main"], b"jjlq");
    assert_eq!(built.status.code(), Some(0), "{}", text(&built.stderr));
    assert_eq!(ran.status.code(), Some(0), "{}", text(&ran.stderr));
    assert_eq!(text(&built.stderr), "");
    assert!(!built.stdout.is_empty());
    assert_eq!(text(&built.stdout), text(&ran.stdout));
    if let Some(symbols) = rust_symbols(&exe) {
        assert!(
            !of_modules(&symbols, &["machine", "code", "codec"]).is_empty(),
            "no machine found: the check of `--native` executables can't see it"
        );
        assert!(of_modules(&symbols, &["linked"]).is_empty());
    }
    plays_in_a_terminal(&exe);
}

/// In a terminal, the roguelike `exe` starts in keys mode, moves, and `q`
/// quits it with the terminal put back and its ending on the normal
/// screen. Nothing where there's no pseudo-terminal.
fn plays_in_a_terminal(exe: &Path) {
    #[cfg(unix)]
    {
        let Some(mut s) = pty::Session::start(&[exe.as_os_str()], false) else {
            return;
        };
        s.wait_for_keys_mode(true);
        pty::assert_keys_mode_settings(&s.settings());
        s.wait_for_screen("\x1b[33m@");
        s.type_keys(b"jjl");
        s.type_keys(b"q");
        let (code, errors) = s.wait();
        assert_eq!(code, 0, "{errors}");
        s.assert_restored();
        let screen = s.screen();
        let left = screen
            .rfind(pty::LEAVE_SCREEN)
            .expect("left the alternate screen");
        // The ending is printed on the normal screen.
        assert!(left < screen.len() - pty::LEAVE_SCREEN.len(), "{screen:?}");
    }
    #[cfg(not(unix))]
    let _ = exe;
}

/// The Rust symbols `exe` defines, demangled by `nm -C`: `None`, having
/// said the check is skipped, if there's no `nm`.
fn rust_symbols(exe: &Path) -> Option<Vec<String>> {
    let Ok(listed) = Command::new("nm").arg("-C").arg(exe).output() else {
        eprintln!("skipped the symbol check: no nm");
        return None;
    };
    assert!(listed.status.success(), "{}", text(&listed.stderr));
    let symbols: Vec<String> = text(&listed.stdout)
        .lines()
        .filter_map(|line| line.splitn(3, ' ').nth(2))
        .map(str::to_string)
        .collect();
    // Demangled: the runtime's own functions are there by their paths.
    assert!(
        symbols
            .iter()
            .any(|name| name.starts_with("stitchwort_rt::")),
        "nm -C demangled nothing"
    );
    Some(symbols)
}

/// Those of `symbols` defined in `stitchwort_rt`'s `modules`: functions
/// of the module (`stitchwort_rt::machine::…`) and methods of its types
/// (`<stitchwort_rt::machine::Machine …>::…`). Not a generic of another
/// module's, such as the standard library's, merely given one of the
/// module's types: the compiler merges identical instantiations under one
/// of their names, which may be the machine's (`Runner<Machine>`'s
/// closure for `Runner<NativeExecutor>`'s), with none of the machine's own
/// code.
fn of_modules<'s>(symbols: &'s [String], modules: &[&str]) -> Vec<&'s String> {
    symbols
        .iter()
        .filter(|name| {
            let name = name.strip_prefix('<').unwrap_or(name);
            modules
                .iter()
                .any(|module| name.starts_with(&format!("stitchwort_rt::{module}::")))
        })
        .collect()
}

/// In a terminal: `q` ends the walking example, and Ctrl-C a program waiting
/// for a key, and either way the terminal's settings are put back (the
/// runtime library's restore guard and signal thread, as for `run`).
#[cfg(unix)]
#[test]
fn the_terminal_is_put_back_after_q_and_after_ctrl_c() {
    if !have_cc() {
        return;
    }
    let dir = work_dir("terminal");
    std::fs::write(
        dir.join("walk.sw"),
        include_str!("../../../../examples/accept/terminal-walk.sw"),
    )
    .expect("write the source");
    build(&dir, &["walk.sw", "--cache-dir", CACHE]);
    let walk = dir.join("walk");
    let Some(mut s) = pty::Session::start(&[walk.as_os_str()], false) else {
        return;
    };
    s.wait_for_keys_mode(true);
    pty::assert_keys_mode_settings(&s.settings());
    s.wait_for_screen("#\x1b[33m@");
    s.type_keys(b"l");
    s.wait_for_screen("#.\x1b[33m@");
    s.type_keys(b"q");
    let (code, errors) = s.wait();
    assert_eq!(code, 0, "{errors}");
    s.assert_restored();
    s.wait_for_screen("The @ stopped at column 1, row 0.");
    drop(s);

    std::fs::write(
        dir.join("interrupt.sw"),
        "import Std (IO)\n\n\
         def main(): {IO} () :=\n  \
           IO.keysMode True\n  \
           let _ := IO.readBytes()\n  \
           IO.print \"not reached\"\n",
    )
    .expect("write the source");
    build(&dir, &["interrupt.sw", "--cache-dir", CACHE]);
    let interrupt = dir.join("interrupt");
    let Some(mut s) = pty::Session::start(&[interrupt.as_os_str()], false) else {
        return;
    };
    s.wait_for_keys_mode(true);
    // Ctrl-C: `ISIG` is on, so the terminal sends `SIGINT`.
    s.type_keys(b"\x03");
    let (code, errors) = s.wait();
    // Ended by `SIGINT` (2), as the shell reports it.
    assert_eq!(code, 130, "{errors}");
    s.assert_restored();
    s.wait_for_screen(pty::LEAVE_SCREEN);
    assert!(!s.screen().contains("not reached"));
}

// ------------------------------------------------------- build --native
//
// Stage S5: the bodies `main` reaches compiled into the executable, where
// they compile (every one but the entry, since stage N4), with the machine
// for the rest (D1287). These need a
// `stitchwort` with the `native` feature, which the test tiers build
// (`--features stitchwort-cli/native`).

/// A file of bench/native.
#[cfg(feature = "native")]
fn native_bench(name: &str) -> String {
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../bench/native")
        .join(name);
    std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("{}: {e}", path.display()))
}

/// The crossing's trampolines (`sw_cross_<number of arguments>`) the
/// executable `exe` defines: the native code linked into it.
#[cfg(feature = "native")]
fn native_trampolines(exe: &Path) -> Vec<String> {
    use object::{Object as _, ObjectSymbol as _};
    let bytes = std::fs::read(exe).expect("read the executable");
    let file = object::File::parse(&*bytes).expect("parse the executable");
    let mut trampolines: Vec<String> = file
        .symbols()
        .filter_map(|symbol| symbol.name().ok())
        .map(|name| name.trim_start_matches('_').to_string())
        .filter(|name| name.starts_with("sw_cross_"))
        .collect();
    trampolines.sort();
    trampolines
}

/// On macOS, `codesign -v` passes on `exe`.
#[cfg(feature = "native")]
fn assert_signed(exe: &Path) {
    if cfg!(target_os = "macos") {
        match Command::new("codesign").arg("-v").arg(exe).output() {
            Ok(verified) => assert!(verified.status.success(), "{}", text(&verified.stderr)),
            Err(e) => eprintln!("skipped the signature check: no codesign ({e})"),
        }
    }
}

/// Builds `source` as `name` in `dir` with `--native`, and checks that the
/// executable's output, errors and exit status on `input` are those of
/// `run --native` and of `run`, and that it's signed. Returns the
/// executable and what it did.
#[cfg(feature = "native")]
fn native_same_as_run(dir: &Path, name: &str, source: &str, input: &[u8]) -> (PathBuf, Output) {
    std::fs::write(dir.join(name), source).expect("write the source");
    build(
        dir,
        &[name, "--native", "--cache-dir", CACHE, "-o", "program"],
    );
    let exe = dir.join("program");
    let built = run_executable(&exe, input);
    for runner in [
        &["run", "--native", "--cache-dir", CACHE, name][..],
        &["run", "--cache-dir", CACHE, name],
    ] {
        let ran = stitchwort(dir, runner, input);
        assert_eq!(
            text(&built.stdout),
            text(&ran.stdout),
            "standard output, {runner:?}"
        );
        assert_eq!(
            text(&built.stderr),
            text(&ran.stderr),
            "standard error, {runner:?}"
        );
        assert_eq!(
            built.status.code(),
            ran.status.code(),
            "exit status, {runner:?}"
        );
    }
    assert_signed(&exe);
    (exe, built)
}

/// A native benchmark at its small size, `name` in bench/native: the same
/// as `run --native` and `run`, printing `expected`, with native code
/// linked in. One test each, so they run in parallel.
#[cfg(feature = "native")]
fn native_benchmark(name: &str, expected: &str) {
    if !have_cc() {
        return;
    }
    let dir = work_dir(&format!("native-{name}"));
    let (exe, built) = native_same_as_run(&dir, name, &native_bench(name), b"");
    assert_eq!(text(&built.stdout), expected, "{name}");
    assert_eq!(built.status.code(), Some(0), "{name}");
    assert!(
        !native_trampolines(&exe).is_empty(),
        "{name} has no native code"
    );
}

#[cfg(feature = "native")]
#[test]
fn native_micro_call_runs_as_it_does_under_run() {
    native_benchmark("micro_call.sw", "20000\n");
}

#[cfg(feature = "native")]
#[test]
fn native_micro_tail_runs_as_it_does_under_run() {
    native_benchmark("micro_tail.sw", "499500\n");
}

#[cfg(feature = "native")]
#[test]
fn native_set_nat_runs_as_it_does_under_run() {
    native_benchmark("set_nat.sw", "1000\n");
}

#[cfg(feature = "native")]
#[test]
fn native_closures_run_as_they_do_under_run() {
    native_benchmark("closures.sw", "36673290\n");
}

/// A map built and drained: the copies taking reuse tokens
/// (crates/rt/src/reuse.rs) are compiled into the executable, which calls
/// them as `run --native` does, and the plain build, which embeds the
/// lowered program, prints the same.
#[cfg(feature = "native")]
#[test]
fn native_executables_keep_the_copies_that_reuse_cells() {
    use object::{Object as _, ObjectSymbol as _};
    if !have_cc() {
        return;
    }
    let source = r#"import Std (IO, List, Map, Nat, Option)

def build (keys: List Nat): Map Nat Nat :=
  List.foldLeft keys Map.empty (m i => Map.insert m i i)

def drain: Nat → Map Nat Nat → Nat
  | Zero, m => 0
  | Succ fuel, m => match Map.popMin m with
    | None => 0
    | Some found => found.fst.snd + drain fuel found.snd

def main(): {IO} () :=
  IO.print "${drain 2000 (build ((List.range 0 1000).map (i => (i * 7919) % 1009)))}"
"#;
    let dir = work_dir("native-reuse");
    let (exe, built) = native_same_as_run(&dir, "maps.sw", source, b"");
    assert_eq!(text(&built.stdout), "504678\n");
    let bytes = std::fs::read(&exe).expect("read the executable");
    let file = object::File::parse(&*bytes).expect("parse the executable");
    let copies: Vec<String> = file
        .symbols()
        .filter_map(|symbol| symbol.name().ok())
        .filter(|name| name.contains("[reuse]#"))
        .map(str::to_string)
        .collect();
    for copy in [
        "Std.Map.Tree.balance[reuse]#",
        "Std.Map.Tree.minView[reuse]#",
    ] {
        assert!(
            copies.iter().any(|c| c.contains(copy)),
            "no {copy} in {copies:?}"
        );
    }
    let (_, plain) = same_as_run(&dir, "maps.sw", source, &[b""]);
    assert_eq!(text(&plain.stdout), "504678\n");
}

/// `--verbose` says how many bodies were compiled: every one `main`
/// reaches, effects included since stage N4 and the entry since stage NO4
/// of docs/proposals/native-only.md.
#[cfg(feature = "native")]
#[test]
fn verbose_says_what_was_compiled() {
    if !have_cc() {
        return;
    }
    let dir = work_dir("native-verbose");
    let build_verbose = |name: &str, source: &str| {
        std::fs::write(dir.join(name), source).expect("write");
        let output = stitchwort(
            &dir,
            &["build", name, "--native", "--verbose", "--cache-dir", CACHE],
            b"",
        );
        assert!(output.status.success(), "{}", text(&output.stderr));
        text(&output.stderr)
    };
    let said = build_verbose("micro_call.sw", &native_bench("micro_call.sw"));
    assert!(
        said.starts_with("native: compiled 4 of the 4 bodies `main` reaches (frames of at most "),
        "{said}"
    );
    assert_eq!(said.lines().count(), 1, "{said}");
    assert!(!native_trampolines(&dir.join("micro_call")).is_empty());

    // A function that performs effects.
    let said = build_verbose(
        "countdown.sw",
        "import Std (IO, Nat)\n\n\
         def countdown: Nat -> {IO} ()\n  \
           | 0 => IO.print \"go\"\n  \
           | Succ n =>\n    \
             IO.print (Nat.toText (Succ n))\n    \
             countdown n\n\n\
         def main(): {IO} () := countdown 2\n",
    );
    assert!(
        said.starts_with("native: compiled 3 of the 3 bodies `main` reaches (frames of at most "),
        "{said}"
    );
    assert!(!native_trampolines(&dir.join("countdown")).is_empty());
    assert_eq!(
        text(&run_executable(&dir.join("countdown"), b"").stdout),
        "2\n1\ngo\n"
    );

    // Nothing but the entry, which is compiled too (stage NO4 of
    // native-only.md).
    let said = build_verbose(
        "hello.sw",
        "import Std (IO)\n\ndef main(): {IO} () := IO.print \"hello\"\n",
    );
    assert!(
        said.starts_with("native: compiled 1 of the 1 bodies `main` reaches (frames of at most "),
        "{said}"
    );
    assert!(!native_trampolines(&dir.join("hello")).is_empty());
    assert_eq!(
        text(&run_executable(&dir.join("hello"), b"").stdout),
        "hello\n"
    );
}

/// An unhandled `Fail`: as under `run`, built with `--native`.
#[cfg(feature = "native")]
#[test]
fn a_failing_program_built_native_fails_as_it_does_under_run() {
    if !have_cc() {
        return;
    }
    let dir = work_dir("native-fail");
    let (_, failed) = native_same_as_run(
        &dir,
        "fail.sw",
        include_str!("../../../../examples/accept/main-fail.sw"),
        b"",
    );
    assert_eq!(failed.status.code(), Some(1));
    assert!(text(&failed.stderr).starts_with("error: "));
}

/// Recursion past the frame limit in native code: as under `run` (the
/// out-of-frames report without the excerpt of `main`'s source, which the
/// executable doesn't have).
#[cfg(feature = "native")]
#[test]
fn native_code_out_of_frames_reports_as_run_does() {
    if !have_cc() {
        return;
    }
    let dir = work_dir("native-frames");
    let source = "import Std (Nat)\n\n\
                  def count : Nat -> Nat\n  \
                    | 0      => 0\n  \
                    | Succ n => 2 * count n\n\n\
                  def main () : {IO} () :=\n  \
                    IO.print (Nat.toText (count (20 * 1000 * 1000)))\n";
    std::fs::write(dir.join("runaway.sw"), source).expect("write the source");
    // Running out at the default 16 million frames touches about 6 GB of
    // stack; a ceiling of one
    // million reports the same way for about 0.4 GB.
    let low = [("STITCHWORT_NATIVE_FRAMES", "1000000")];
    let built = stitchwort_with_env(
        &dir,
        &["build", "runaway.sw", "--native", "--cache-dir", CACHE],
        b"",
        &low,
    );
    assert!(built.status.success(), "{}", text(&built.stderr));
    let exe = dir.join("runaway");
    assert!(!native_trampolines(&exe).is_empty(), "`count` is compiled");
    let built = run_executable(&exe, b"");
    assert_eq!(built.status.code(), Some(2));
    assert_eq!(text(&built.stdout), "");
    let stderr = text(&built.stderr);
    assert!(
        stderr.starts_with("[E-RESOURCE] Error: ran out of resources: "),
        "{stderr}"
    );
    // The machine's note on where the recursion was deepest, from the
    // frames that left native code with the error (stage NO5 of
    // native-only.md). The count is native code's own depth budget, 16
    // million frames (`Limits::native_frames`, D3450) lowered to one million
    // by the environment, not the machine's.
    assert!(
        stderr.contains(
            "\n  note: the recursion was deepest in `Main.count` (999999 frames pending)\n"
        ),
        "{stderr}"
    );
    for runner in [
        &["run", "--native", "--cache-dir", CACHE, "runaway.sw"][..],
        &["run", "--cache-dir", CACHE, "runaway.sw"],
    ] {
        let ran = stitchwort_with_env(&dir, runner, b"", &low);
        assert_eq!(ran.status.code(), Some(2), "{runner:?}");
        assert_eq!(text(&ran.stdout), text(&built.stdout), "{runner:?}");
        // The same message and notes as `run`'s report.
        let ran_stderr = text(&ran.stderr);
        for line in stderr.lines() {
            let line = line
                .trim_start_matches("[E-RESOURCE] Error: ")
                .trim_start_matches("  note: ");
            // The depth differs: the machine stops at 2 million frames.
            if line.ends_with(" frames pending)")
                && runner == &["run", "--cache-dir", CACHE, "runaway.sw"][..]
            {
                continue;
            }
            assert!(ran_stderr.contains(line), "{line:?} isn't in {ran_stderr}");
        }
    }
}

/// Milestone M2: the roguelike built with `--native` runs every body
/// natively (its entry too since stage NO4), and plays as under `run`, piped
/// and in a terminal, with no machine inside (stage NO6).
#[cfg(feature = "native")]
#[test]
fn the_roguelike_built_native_plays_as_it_does_under_run() {
    if !have_cc() {
        return;
    }
    let dir = work_dir("rogue-native");
    let project = seeded_rogue(&dir);
    let output = stitchwort(
        &dir,
        &[
            "build",
            "rogue",
            "--native",
            "--verbose",
            "-o",
            "rogue-game",
        ],
        b"",
    );
    assert!(output.status.success(), "{}", text(&output.stderr));
    let said = text(&output.stderr);
    let counts = said
        .strip_prefix("native: compiled ")
        .and_then(|rest| rest.split_once(" bodies `main` reaches"))
        .and_then(|(counts, _)| counts.split_once(" of the "))
        .map(|(compiled, reached)| (compiled.parse::<usize>(), reached.parse::<usize>()));
    let Some((Ok(compiled), Ok(reached))) = counts else {
        panic!("{said}");
    };
    assert_eq!(compiled, reached, "every body, the entry included: {said}");
    assert_eq!(said.lines().count(), 1, "{said}");
    let exe = dir.join("rogue-game");
    assert_signed(&exe);
    assert!(!native_trampolines(&exe).is_empty());
    let built = run_executable(&exe, b"jjlq");
    let ran = stitchwort(&project, &["run", "Rogue.main"], b"jjlq");
    assert_eq!(built.status.code(), Some(0), "{}", text(&built.stderr));
    assert_eq!(ran.status.code(), Some(0), "{}", text(&ran.stderr));
    assert_eq!(text(&built.stderr), "");
    assert!(!built.stdout.is_empty());
    assert_eq!(text(&built.stdout), text(&ran.stdout));
    // No machine inside (stage NO6 of docs/proposals/native-only.md): none
    // of the machine, the bytecode compiler or the codec is linked, and
    // the tables and literals are read instead.
    if let Some(symbols) = rust_symbols(&exe) {
        let machine = of_modules(&symbols, &["machine", "code", "codec"]);
        assert!(machine.is_empty(), "{machine:#?}");
        assert!(!of_modules(&symbols, &["linked"]).is_empty());
    }
    plays_in_a_terminal(&exe);
}

/// A guard (stage NO3 of docs/proposals/native-only.md, kept where NO5
/// left something to check): `run --native` runs every body natively and
/// the machine runs nothing, and the roguelike's frame bound gets a native
/// frame limit well above the machine's (D1299, D3450), so `build --native`
/// sizes a stack for it. The frames' bound, the limit and the stack are
/// printed, so the margin is in the test's output.
#[cfg(feature = "native")]
#[test]
fn the_roguelike_runs_natively() {
    let dir = work_dir("rogue-guard");
    let project = seeded_rogue(&dir);
    let ran = stitchwort(
        &project,
        &["run", "--native", "--verbose", "Rogue.main"],
        b"jjlq",
    );
    let said = text(&ran.stderr);
    assert_eq!(ran.status.code(), Some(0), "{said}");
    assert!(
        said.contains("native: the machine executed 0 instructions"),
        "{said}"
    );
    let running = said
        .lines()
        .find(|line| line.starts_with("native: running "))
        .unwrap_or_else(|| panic!("nothing ran natively: {said}"));
    let bound = running
        .split_once("(frames of at most ")
        .and_then(|(_, rest)| rest.split_once(" bytes"))
        .and_then(|(bytes, _)| bytes.parse::<usize>().ok())
        .unwrap_or_else(|| panic!("no frame bound: {running}"));
    // Native code's depth budget: the default ceiling, or less if the
    // roguelike's frames are too wide for the cap (its widest are 4.8 KB,
    // so about 14 million frames). It must stay well above the machine's.
    let default = stitchwort_rt::Limits::from_core(Default::default());
    let limit = default.for_native(bound).frames;
    assert!(
        limit > 4 * default.frames && limit <= default.native_frames,
        "{limit} frames: {running}"
    );
    let stack = stitchwort_rt::native_abi::native_stack(limit as u64, bound)
        .unwrap_or_else(|| panic!("over the cap: {running}"));
    println!(
        "the roguelike's frames: at most {bound} bytes, {limit} of them: a stack of {stack} bytes, of the {} cap",
        stitchwort_rt::native_abi::STACK_CAP
    );
    assert!(
        stack as u64 <= stitchwort_rt::native_abi::STACK_CAP,
        "{running}"
    );

    if !have_cc() {
        return;
    }
    let output = stitchwort(
        &dir,
        &[
            "build",
            "rogue",
            "--native",
            "--verbose",
            "-o",
            "rogue-guard",
        ],
        b"",
    );
    let said = text(&output.stderr);
    assert!(output.status.success(), "{said}");
    assert!(
        said.contains(&format!(", a stack of {} MiB, ", stack / (1024 * 1024))),
        "{said}"
    );
}

/// A recursive function whose frames are too wide for the default native
/// frame limit to fit the stack cap (D1299 of
/// docs/proposals/native-only.md): it isn't refused, but gets a smaller
/// limit (`native_abi::native_frame_limit`, D3450), so `run --native` and
/// `build --native` run it.
#[cfg(feature = "native")]
#[test]
fn a_program_with_wide_frames_gets_a_smaller_native_limit() {
    let dir = work_dir("native-cap");
    // 400 arguments, each live across the call: frames of tens of KB.
    let width = 400;
    let names: Vec<String> = (0..width).map(|i| format!("a{i}")).collect();
    let source = format!(
        "import Std (IO, Nat)\n\n\
         def wide: {}\n  \
           | Zero, {} => a0\n  \
           | Succ p, {} => 1 + wide p {}\n\n\
         def main(): {{IO}} () := IO.print (Nat.toText (wide 3 {}))\n",
        vec!["Nat"; width + 2].join(" → "),
        names.join(", "),
        names.join(", "),
        names.join(" "),
        vec!["7"; width].join(" "),
    );
    std::fs::write(dir.join("wide.sw"), source).expect("write the source");
    let ran = stitchwort(
        &dir,
        &[
            "run",
            "--native",
            "--verbose",
            "--cache-dir",
            CACHE,
            "wide.sw",
        ],
        b"",
    );
    let said = text(&ran.stderr);
    assert_eq!(text(&ran.stdout), "10\n", "{said}");
    assert!(
        said.contains("native: the machine executed 0 instructions"),
        "{said}"
    );
    if !have_cc() {
        return;
    }
    build(&dir, &["wide.sw", "--native", "--cache-dir", CACHE]);
    let built = run_executable(&dir.join("wide"), b"");
    assert_eq!(text(&built.stdout), "10\n", "{}", text(&built.stderr));
}

/// A failed layout probe (forced by its test hook,
/// `STITCHWORT_TEST_LAYOUT_PROBE_FAILS`): `build --native` fails with the
/// probe's message and writes nothing, `run --native` refuses the run, and
/// an executable built before refuses to start (stage NO5 of
/// docs/proposals/native-only.md §4).
#[cfg(feature = "native")]
#[test]
fn a_failed_layout_probe_fails_the_build() {
    let dir = work_dir("native-probe");
    std::fs::write(
        dir.join("hello.sw"),
        "import Std (IO)\n\ndef main(): {IO} () := IO.print \"hello\"\n",
    )
    .expect("write the source");
    let probe = stitchwort_rt::native_abi::PROBE_FAILS;
    let message = format!("the layout of values isn't as native code expects: forced by {probe}\n");
    let with_probe_failing = |args: &[&str]| {
        let mut command = Command::new(env!("CARGO_BIN_EXE_stitchwort"));
        command.current_dir(&dir).args(args).env(probe, "1");
        run_with_input(command, b"")
    };
    let ran = with_probe_failing(&["run", "--native", "--cache-dir", CACHE, "hello.sw"]);
    assert_eq!(ran.status.code(), Some(1));
    assert_eq!(text(&ran.stderr), format!("error: {message}"));
    assert_eq!(text(&ran.stdout), "");
    // The machine doesn't probe.
    let ran = with_probe_failing(&["run", "--cache-dir", CACHE, "hello.sw"]);
    assert_eq!(text(&ran.stdout), "hello\n");
    if !have_cc() {
        return;
    }
    let built = with_probe_failing(&["build", "hello.sw", "--native", "--cache-dir", CACHE]);
    assert_eq!(built.status.code(), Some(1));
    assert_eq!(text(&built.stderr), format!("error: {message}"));
    assert!(!dir.join("hello").exists(), "an executable was written");

    build(&dir, &["hello.sw", "--native", "--cache-dir", CACHE]);
    let mut command = Command::new(dir.join("hello"));
    command.env(probe, "1");
    let started = run_with_input(command, b"");
    assert_eq!(started.status.code(), Some(2));
    assert_eq!(
        text(&started.stderr),
        format!("internal error: this executable can't run: {message}")
    );
    assert_eq!(text(&started.stdout), "");
}

/// The self-hosted formatter's project (`tools/fmt`).
const FMT: &str = concat!(env!("CARGO_MANIFEST_DIR"), "/../../tools/fmt");

/// A Stitchwort file the formatter leaves alone, and one it rewrites to it.
const TIDY: &str = "def add (a b: Nat): Nat := a + b\n";
const UNTIDY: &str = "def add (a: Nat) (b: Nat): Nat := a+b\n";
const BROKEN: &str = "def x :=";

/// Lays out the fixture folder `work/src`: a file to rewrite, a formatted
/// one, one that doesn't parse, and one in a nested folder.
fn fmt_fixture(work: &Path) {
    for (name, text) in [
        ("src/a.sw", UNTIDY),
        ("src/b.sw", TIDY),
        ("src/bad.sw", BROKEN),
        ("src/deep/c.sw", UNTIDY),
    ] {
        let path = work.join(name);
        std::fs::create_dir_all(path.parent().expect("in a folder")).expect("make the folder");
        std::fs::write(path, text).expect("write the fixture");
    }
}

/// The self-hosted formatter's command line (`Fmt.Twin.main`, `fmt --stage
/// text FILE...`) as `stitchwort run` and as a built executable do it, on a
/// folder of Stitchwort files: it prints each file formatted on standard
/// output and writes nothing, exits 0 when every file was answered, and
/// reports a file that doesn't parse (`[E-PARSE] Error: ...`) or can't be read
/// on standard error and exits 2, still answering the files that do work; a
/// `--batch` list answers for its paths in one run; a bad flag exits 2 with
/// the usage line, and `--help` 0. (Under its old stand-in, the toy
/// formatter, this also covered `--check`, in-place rewriting and walking
/// folders, which the self-hosted formatter's command line doesn't do.)
#[test]
fn fmt_answers_for_a_folder_of_files_under_run_and_built() {
    if !have_cc() {
        return;
    }
    let work = work_dir("fmt");
    let bin = work.join("bin");
    std::fs::create_dir_all(&bin).expect("make the folder");
    let target = "Fmt.Twin.main";
    let mut builds: Vec<(&str, Vec<&str>)> = vec![("plain", vec![])];
    if cfg!(feature = "native") {
        builds.push(("native", vec!["--native"]));
    }
    let mut runners: Vec<(String, Option<PathBuf>)> = vec![("run".into(), None)];
    for (name, flags) in &builds {
        let exe = bin.join(name);
        let mut args = vec!["build", target, "--project", FMT, "--cache-dir", CACHE];
        args.extend(flags);
        args.extend(["-o", exe.to_str().expect("a path")]);
        let output = stitchwort(&work, &args, b"");
        assert!(
            output.status.success(),
            "build failed: {}",
            text(&output.stderr)
        );
        runners.push((name.to_string(), Some(exe)));
    }
    for (runner, exe) in runners {
        let folder = work.join(&runner);
        fmt_fixture(&folder);
        // `fmt ARGS` in `folder`: what it printed, and its exit code.
        let fmt = |args: &[&str]| -> (String, String, Option<i32>) {
            let output = match &exe {
                Some(exe) => {
                    let mut command = Command::new(exe);
                    command.args(args).current_dir(&folder);
                    run_with_input(command, b"")
                }
                None => {
                    let mut all = vec!["run", "--cache-dir", CACHE, "--project", FMT, target, "--"];
                    all.extend(args);
                    stitchwort(&folder, &all, b"")
                }
            };
            (
                text(&output.stdout),
                text(&output.stderr),
                output.status.code(),
            )
        };
        let before_a = std::fs::read_to_string(folder.join("src/a.sw")).expect("read a.sw");
        let refusal = "[E-PARSE] Error: expected a parameter such as `(x: Nat)`, or `:` and the \
                       definition's type, but found `:=`";
        let parse_error = "[E-PARSE] Error: expected a parameter";

        let (out, err, code) = fmt(&["--stage", "text", "src/a.sw", "src/b.sw", "src/deep/c.sw"]);
        assert_eq!(
            (out.as_str(), err.as_str(), code),
            (&format!("{TIDY}{TIDY}{TIDY}")[..], "", Some(0)),
            "{runner}: formatted, on standard output"
        );
        assert_eq!(
            std::fs::read_to_string(folder.join("src/a.sw")).expect("read a.sw"),
            before_a,
            "{runner}: nothing written"
        );

        let (out, err, code) = fmt(&["src/a.sw"]);
        assert_eq!(
            (out.as_str(), err.as_str(), code),
            (TIDY, "", Some(0)),
            "{runner}: the text stage is the default"
        );

        let (out, err, code) = fmt(&["src/bad.sw", "src/b.sw"]);
        assert_eq!((out.as_str(), code), (TIDY, Some(2)), "{runner}: a refusal");
        assert!(err.starts_with(parse_error), "{runner}: refusal says {err}");

        let (out, err, code) = fmt(&["src/missing.sw", "src/a.sw"]);
        assert_eq!(
            (out.as_str(), code),
            (TIDY, Some(2)),
            "{runner}: unreadable"
        );
        assert!(
            err.starts_with("src/missing.sw: "),
            "{runner}: unreadable says {err}"
        );

        std::fs::write(
            folder.join("list.txt"),
            "src/a.sw\n\nsrc/bad.sw\nsrc/deep/c.sw\n",
        )
        .expect("write the list");
        let (out, err, code) = fmt(&["--batch", "list.txt"]);
        let block = |path: &str, status: u32, body: &str, message: &str| {
            format!(
                "\u{1e}{path}\n\u{1f}{status}\u{1f}{}\u{1f}{message}\n{body}",
                body.chars().count()
            )
        };
        let expected = block("src/a.sw", 0, TIDY, "")
            + &block("src/bad.sw", 2, "", refusal)
            + &block("src/deep/c.sw", 0, TIDY, "");
        assert_eq!(
            (out, err.as_str(), code),
            (expected, "", Some(0)),
            "{runner}: a batch answers for every path, a refusal inside its block"
        );

        let (out, err, code) = fmt(&["--wide", "src"]);
        assert_eq!((out.as_str(), code), ("", Some(2)), "{runner}: bad flag");
        assert!(err.contains("usage: fmt"), "{runner}: usage, got {err}");
        let (out, _, code) = fmt(&["--help"]);
        assert_eq!(code, Some(0), "{runner}: --help");
        assert!(out.starts_with("usage: fmt"), "{runner}: help, got {out}");
    }
}
