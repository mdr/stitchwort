//! `stitchwort build TARGET [-o OUT]`: a standalone executable (stage S3 of
//! docs/proposals/standalone-executables.md, D1287–D1289).
//!
//! It checks and lowers `main` exactly as `run` does, encodes the lowered
//! program with its limits ([`stitchwort_rt::encode`]), and writes it as
//! read-only data in an object file, `program.o`: `sw_program`, with a
//! manifest, `sw_native_manifest`, that names the runtime library's
//! `sw_run_machine` to run it. Then it links that with the runtime library,
//! `libstitchwort_standalone.a` (`crates/standalone`, which has C `main`,
//! the machine and the host), using the system's C compiler as the linker.
//! The executable needs neither `stitchwort` nor the source.
//!
//! With `--native` (stage S5), every body `main` reaches is compiled
//! instead, as `run --native` would compile it (`stitchwort_native::aot`),
//! into the object: the code, the tables and literals it reads in place of
//! the program (stage NO6 of native-only.md: `stitchwort_rt::linked`), and
//! a manifest that names `sw_run_native` and says where they are. The
//! linker drops what nothing reaches, so that executable has no machine,
//! bytecode compiler or codec.

use std::path::{Path, PathBuf};
use std::process::{Command, ExitCode};

use object::write::{Object, StandardSection, Symbol, SymbolSection};
use object::{
    Architecture, BinaryFormat, Endianness, SectionKind, SymbolFlags, SymbolKind, SymbolScope,
};
use stitchwort_cli::project::{analyse, project_sources};
use stitchwort_syntax::ast::Decl;

use super::{
    CacheArgs, discard, load_main, locate_project, new_session, project_name, refuse_open_goals,
    report,
};

/// The runtime library's file name.
pub const LIBRARY: &str = "libstitchwort_standalone.a";

/// The environment variable that names the runtime library, overriding
/// where `build` looks for it.
pub const LIBRARY_VARIABLE: &str = "STITCHWORT_RUNTIME";

/// The native libraries the runtime library needs on the link line: what
/// `rustc --print native-static-libs` lists for it (on macOS, rustc 1.99:
/// `-liconv -lSystem -lc -lm`). A test checks these against rustc's list for
/// the standard library.
pub const NATIVE_LIBS: &[&str] = if cfg!(target_os = "macos") {
    &["-liconv", "-lSystem", "-lc", "-lm"]
} else {
    &[
        "-lgcc_s",
        "-lutil",
        "-lrt",
        "-lpthread",
        "-lm",
        "-ldl",
        "-lc",
    ]
};

/// The linker flag that drops what nothing reaches, which is most of the
/// library (the static library holds all of `std`).
const DEAD_STRIP: &str = if cfg!(target_os = "macos") {
    "-Wl,-dead_strip"
} else {
    "-Wl,--gc-sections"
};

/// `build TARGET [-o OUT]`: `TARGET` is a file, a project folder (whose one
/// namespace with a `main` is built), or the full name of a function in the
/// project. `OUT` is, by default, the file's or folder's name, or the
/// function's namespace's, in the current folder. `native`: with
/// `--native`, `Some(verbose)`: the bodies `main` reaches are compiled
/// into the object where they compile, and with `verbose` it says on standard
/// error what was compiled, and why anything wasn't.
pub fn build_executable(
    target: &str,
    out: Option<&Path>,
    project: Option<&Path>,
    native: Option<bool>,
    cache: &CacheArgs,
) -> ExitCode {
    #[cfg(not(feature = "native"))]
    if native.is_some() {
        eprintln!(
            "error: this `stitchwort` was built without native code; build it with `--features native`"
        );
        return ExitCode::FAILURE;
    }
    let (entry, project, default_name) = if Path::new(target).is_dir() {
        if project.is_some() {
            eprintln!(
                "error: `{target}` is a project folder: give the project once, as the target or \
                 with --project"
            );
            return ExitCode::FAILURE;
        }
        let dir = Path::new(target);
        let Some(entry) = project_entry(dir) else {
            return ExitCode::FAILURE;
        };
        (entry, Some(dir), project_name(dir))
    } else if super::is_file_target(target) {
        let stem = Path::new(target)
            .file_stem()
            .map_or("main".into(), |s| s.to_string_lossy().into_owned());
        (target.to_string(), None, stem)
    } else {
        (target.to_string(), project, namespace_name(target))
    };
    let out = out.map_or_else(|| PathBuf::from(default_name), Path::to_path_buf);
    if out.is_dir() {
        // Building a project folder from the folder it's in, say.
        eprintln!(
            "error: can't write the executable to {}: it's a folder\n  note: name the \
             executable with -o",
            out.display()
        );
        return ExitCode::FAILURE;
    }
    let (session, main, goals) = match load_main(&entry, project, cache) {
        Ok(loaded) => loaded,
        Err(code) => return code,
    };
    if refuse_open_goals(goals) {
        return ExitCode::FAILURE;
    }
    let program = match session.lower_fast(&main) {
        Ok(program) => program,
        Err(e) => {
            report(&session.sources, &[e.diagnostic(&main)]);
            return ExitCode::FAILURE;
        }
    };
    let limits = stitchwort_rt::Limits::from_core(session.elab.limits);
    discard(session);
    let object = match native {
        Some(verbose) => match native_object(&program, &limits, verbose) {
            Some(object) => object,
            None => return ExitCode::FAILURE,
        },
        None => program_object(&stitchwort_rt::encode(&program, &limits)),
    };
    match link(&object, &out) {
        Ok(()) => ExitCode::SUCCESS,
        Err(message) => {
            eprint!("{message}");
            ExitCode::FAILURE
        }
    }
}

/// The function a project folder's executable runs: `main` of the one
/// namespace that declares one. `None`, having said why, if there isn't
/// exactly one.
fn project_entry(dir: &Path) -> Option<String> {
    let project = locate_project(Some(dir), "build", "build hello.sw")?;
    let mut session = new_session(false);
    let sources = match project_sources(&project.files, &project.name, &mut session.sources) {
        Ok(sources) => sources,
        Err(diagnostics) => {
            report(&session.sources, &diagnostics);
            return None;
        }
    };
    let analysis = analyse(&mut session, &project.name, sources);
    if !analysis.diagnostics.is_empty() {
        report(&session.sources, &analysis.diagnostics);
        return None;
    }
    let with_main: Vec<&str> = analysis
        .namespaces
        .iter()
        .filter(|namespace| {
            namespace.modules.iter().any(|module| {
                module
                    .decls
                    .iter()
                    .any(|decl| matches!(decl, Decl::Signature { name, .. } if name.text == "main"))
            })
        })
        .map(|namespace| namespace.name.as_str())
        .collect();
    let example = |namespace: &str| {
        format!(
            "stitchwort build {namespace}.main --project {}",
            dir.display()
        )
    };
    match with_main[..] {
        [namespace] => Some(format!("{namespace}.main")),
        [] => {
            eprintln!(
                "error: no namespace of project {}/ declares `main`",
                project.name
            );
            eprintln!(
                "  note: name the function to build, as in `{}`",
                example("Name")
            );
            None
        }
        [first, ..] => {
            eprintln!(
                "error: more than one namespace of project {}/ declares `main`: {}",
                project.name,
                with_main.join(", ")
            );
            eprintln!("  note: name the one to build, as in `{}`", example(first));
            None
        }
    }
}

/// The default name of the executable for a function of the project: its
/// namespace's last part, in lower case (`Rogue.main` gives `rogue`).
fn namespace_name(function: &str) -> String {
    let mut parts = function.rsplit('.');
    parts.next();
    parts
        .next()
        .map_or("main".to_string(), str::to_ascii_lowercase)
}

/// `build --native`: the object of [`finish_object`], with the native code
/// of every body `main` reaches (`stitchwort_native::aot`), or, if any
/// can't be compiled, `None`, having said why (stage NO5 of
/// docs/proposals/native-only.md: the executable has no machine to fall
/// back to). With `verbose`, says what was compiled.
#[cfg(feature = "native")]
fn native_object(
    program: &stitchwort_rt::Program,
    limits: &stitchwort_rt::Limits,
    verbose: bool,
) -> Option<Vec<u8>> {
    let image = stitchwort_rt::code::compile(program);
    let tables = stitchwort_rt::linked::encode(program, &image, limits);
    let options = stitchwort_native::n1::Options {
        trace_refcounts: false,
    };
    match stitchwort_native::aot::compile_object(
        program,
        &image,
        &tables,
        options,
        limits.frames as u64,
    ) {
        Ok(code) => {
            if verbose {
                for line in code.report() {
                    eprintln!("{line}");
                }
            }
            Some(finish_object(code.object))
        }
        Err(why) => {
            let mut lines = why.iter();
            if let Some(message) = lines.next() {
                eprintln!("error: {message}");
            }
            for note in lines {
                eprintln!("  note: {note}");
            }
            None
        }
    }
}

#[cfg(not(feature = "native"))]
fn native_object(
    _program: &stitchwort_rt::Program,
    _limits: &stitchwort_rt::Limits,
    _verbose: bool,
) -> Option<Vec<u8>> {
    unreachable!("`build --native` is refused without the `native` feature")
}

/// The object file of an executable built without `--native`: the encoded
/// program, `sw_program`, and a manifest (`stitchwort_rt::native_aot`)
/// that names the runtime library's `sw_run_machine` to run it on the
/// machine, with no code. See [`finish_object`].
pub fn program_object(bytes: &[u8]) -> Vec<u8> {
    use object::write::Relocation;
    use object::{RelocationEncoding, RelocationFlags, RelocationKind};
    use stitchwort_rt::native_aot::{Manifest, RUN_MACHINE};
    let format = if cfg!(target_os = "macos") {
        BinaryFormat::MachO
    } else {
        BinaryFormat::Elf
    };
    let architecture = if cfg!(target_arch = "aarch64") {
        Architecture::Aarch64
    } else {
        Architecture::X86_64
    };
    let mut object = Object::new(format, architecture, Endianness::Little);
    let data = object.section_id(StandardSection::ReadOnlyData);
    let program = add_data(&mut object, data, "sw_program", bytes, 1).0;
    // The manifest holds addresses, which the loader fills in.
    let section = object.section_id(StandardSection::ReadOnlyDataWithRel);
    let manifest = Manifest::machine_bytes(bytes.len() as u64);
    let (_, at) = add_data(&mut object, section, "sw_native_manifest", &manifest, 8);
    let run = object.add_symbol(Symbol {
        name: RUN_MACHINE.as_bytes().to_vec(),
        value: 0,
        size: 0,
        kind: SymbolKind::Text,
        scope: SymbolScope::Linkage,
        weak: false,
        section: SymbolSection::Undefined,
        flags: SymbolFlags::None,
    });
    for (offset, symbol) in [(Manifest::RUN_AT, run), (Manifest::DATA_AT, program)] {
        object
            .add_relocation(
                section,
                Relocation {
                    offset: at + offset as u64,
                    symbol,
                    addend: 0,
                    flags: RelocationFlags::Generic {
                        kind: RelocationKind::Absolute,
                        encoding: RelocationEncoding::Generic,
                        size: 64,
                    },
                },
            )
            .expect("an address in data can be relocated");
    }
    finish_object(object)
}

/// Marks `object` (one with no native code, or the native code generator's,
/// with the code, the tables and the manifest) as this platform's linker
/// expects, and writes it.
pub fn finish_object(mut object: Object<'_>) -> Vec<u8> {
    if object.format() == BinaryFormat::MachO {
        // Without it, ld64 warns that the object has no platform and assumes
        // one. The version is the oldest macOS that runs on Apple silicon.
        let mut version = object::write::MachOBuildVersion::default();
        version.platform = object::macho::PLATFORM_MACOS;
        version.minos = object::macho::Version::new(11, 0, 0);
        version.sdk = object::macho::Version::new(11, 0, 0);
        object.set_macho_build_version(version);
    } else {
        // Without it, GNU ld assumes the object needs an executable stack.
        object.add_section(Vec::new(), b".note.GNU-stack".to_vec(), SectionKind::Note);
    }
    object
        .write()
        .expect("an object of data and compiled code can be written")
}

/// Defines the global data symbol `name` as `data`, in `section`: the
/// symbol, and where in the section it is.
fn add_data(
    object: &mut Object<'_>,
    section: object::write::SectionId,
    name: &str,
    data: &[u8],
    align: u64,
) -> (object::write::SymbolId, u64) {
    let symbol = object.add_symbol(Symbol {
        name: name.as_bytes().to_vec(),
        value: 0,
        size: 0,
        kind: SymbolKind::Data,
        scope: SymbolScope::Linkage,
        weak: false,
        section: SymbolSection::Undefined,
        flags: SymbolFlags::None,
    });
    let at = object.add_symbol_data(symbol, section, data, align);
    (symbol, at)
}

/// Links `object` with the runtime library into the executable `out`, with
/// `$CC`, or `cc`. On failure, what to print.
fn link(object: &[u8], out: &Path) -> Result<(), String> {
    let library = find_library()?;
    let dir = TempDir::new()?;
    let object_path = dir.path.join("program.o");
    std::fs::write(&object_path, object)
        .map_err(|e| format!("error: can't write {}: {e}\n", object_path.display()))?;
    let cc = std::env::var_os("CC")
        .filter(|cc| !cc.is_empty())
        .unwrap_or_else(|| "cc".into());
    let mut command = Command::new(&cc);
    command
        .arg(&object_path)
        .arg(&library)
        .args(NATIVE_LIBS)
        .arg(DEAD_STRIP)
        .arg("-o")
        .arg(out);
    let output = match command.output() {
        Ok(output) => output,
        Err(e) if e.kind() == std::io::ErrorKind::NotFound => {
            let install = if cfg!(target_os = "macos") {
                "install Xcode's command line tools (`xcode-select --install`)"
            } else {
                "install a C compiler: `gcc` or `clang` (on Debian or Ubuntu, the \
                 `build-essential` package)"
            };
            return Err(format!(
                "error: can't find a C compiler to link with: there's no `{}` on the PATH\n  \
                 note: `build` links the executable with the system's C compiler (`$CC`, or \
                 `cc`); {install}\n",
                cc.to_string_lossy()
            ));
        }
        Err(e) => {
            return Err(format!(
                "error: can't run `{}` to link: {e}\n",
                cc.to_string_lossy()
            ));
        }
    };
    // Whatever the linker said, as it said it: warnings too.
    let said = format!(
        "{}{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    if !output.status.success() {
        return Err(format!(
            "error: linking failed: `{}` ended with {}\n{said}",
            cc.to_string_lossy(),
            output.status
        ));
    }
    eprint!("{said}");
    Ok(())
}

/// Where the runtime library is: the file `STITCHWORT_RUNTIME` names, or
/// `libstitchwort_standalone.a` beside this `stitchwort`, or in
/// `../lib/stitchwort/` from it (where the Nix package installs it).
fn find_library() -> Result<PathBuf, String> {
    if let Some(path) = std::env::var_os(LIBRARY_VARIABLE) {
        let path = PathBuf::from(path);
        return if path.is_file() {
            Ok(path)
        } else {
            Err(format!(
                "error: there's no runtime library at {}, which {LIBRARY_VARIABLE} names\n",
                path.display()
            ))
        };
    }
    let exe = std::env::current_exe().and_then(|exe| exe.canonicalize());
    let Some(dir) = exe.as_deref().ok().and_then(Path::parent) else {
        return Err(format!(
            "error: can't find the runtime library ({LIBRARY}): this program's own location \
             isn't known\n  note: set {LIBRARY_VARIABLE} to its path\n"
        ));
    };
    let candidates = [
        dir.join(LIBRARY),
        dir.join("..").join("lib").join("stitchwort").join(LIBRARY),
    ];
    if let Some(found) = candidates.iter().find(|path| path.is_file()) {
        return Ok(found.clone());
    }
    Err(format!(
        "error: can't find the runtime library ({LIBRARY}): it isn't at {} or {}\n  \
         note: build it with `cargo build --release -p stitchwort-standalone` (it goes beside \
         `target/release/stitchwort`), or set {LIBRARY_VARIABLE} to its path\n",
        candidates[0].display(),
        candidates[1].display()
    ))
}

/// A fresh temporary directory, removed when dropped.
struct TempDir {
    path: PathBuf,
}

impl TempDir {
    fn new() -> Result<TempDir, String> {
        let nanos = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .map_or(0, |d| d.subsec_nanos());
        let path =
            std::env::temp_dir().join(format!("stitchwort-build-{}-{nanos}", std::process::id()));
        std::fs::create_dir_all(&path)
            .map_err(|e| format!("error: can't make {}: {e}\n", path.display()))?;
        Ok(TempDir { path })
    }
}

impl Drop for TempDir {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.path);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_function_builds_to_its_namespaces_name() {
        assert_eq!(namespace_name("Rogue.main"), "rogue");
        assert_eq!(namespace_name("Aoc.Day05.main"), "day05");
        assert_eq!(namespace_name("main"), "main");
    }

    /// `NATIVE_LIBS` has every library rustc says a static library of the
    /// standard library needs (the runtime library's other dependencies
    /// need none of their own). Skipped without `rustc`.
    #[test]
    fn the_native_libraries_are_the_ones_rustc_lists() {
        let dir = TempDir::new().expect("a temporary folder");
        std::fs::write(dir.path.join("empty.rs"), "").expect("write");
        let printed = Command::new("rustc")
            .args(["--crate-type", "staticlib", "--print", "native-static-libs"])
            .arg("-o")
            .arg(dir.path.join("libempty.a"))
            .arg(dir.path.join("empty.rs"))
            .output();
        let Ok(printed) = printed else {
            eprintln!("skipped: no rustc");
            return;
        };
        let said = String::from_utf8_lossy(&printed.stderr);
        let listed = said
            .lines()
            .find_map(|line| line.split_once("native-static-libs: "))
            .map(|(_, libs)| libs)
            .unwrap_or_else(|| panic!("rustc printed no list: {said}"));
        for lib in listed.split_whitespace() {
            assert!(
                NATIVE_LIBS.contains(&lib),
                "{lib} is missing from {NATIVE_LIBS:?}"
            );
        }
    }

    #[test]
    fn the_object_defines_the_program_and_a_manifest_naming_the_machine() {
        use object::{Object as _, ObjectSymbol as _};
        let bytes = program_object(b"hello");
        let file = object::File::parse(&*bytes).expect("parses");
        let prefix = if cfg!(target_os = "macos") { "_" } else { "" };
        let symbol = |name: &str| {
            file.symbols()
                .find(|s| s.name() == Ok(&format!("{prefix}{name}")))
                .unwrap_or_else(|| panic!("no {name}"))
        };
        for name in ["sw_program", "sw_native_manifest"] {
            let symbol = symbol(name);
            assert!(symbol.is_definition() && symbol.is_global(), "{name}");
        }
        // The way to run it is the library's: the machine.
        assert!(symbol("sw_run_machine").is_undefined());
        assert!(
            file.symbols()
                .all(|s| s.name() != Ok(&format!("{prefix}sw_run_native")))
        );
    }
}
