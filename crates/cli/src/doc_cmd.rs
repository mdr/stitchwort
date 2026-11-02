//! `stitchwort doc NAME` (SW-1019, docs/proposals/documentation.md §5.3):
//! loads what the name needs and prints [`stitchwort_driver::doc`]'s report.
//!
//! The name is resolved, and the header, doc and examples found, from
//! parsing alone. The elaborated type and the theorems need a check, through
//! the check cache, so `--theorems 0` skips it (D2152). For a name of the
//! program only its namespace and the namespaces that use it are checked and
//! searched (D2146); for a library name, the library alone.

use std::collections::BTreeSet;
use std::path::{Path, PathBuf};
use std::process::ExitCode;

use serde::Serialize;
use stitchwort_cli::project::{self, Analysis, DiskFiles, Target, analyse, project_sources};
use stitchwort_driver::doc::{
    Decls, Input, Kind, Matches, Resolution, Within, render_coverage, render_matches,
    render_namespace, render_text,
};
use stitchwort_driver::driver::Session;
use stitchwort_driver::search::Scope;
use stitchwort_syntax::{SourceMap, parse_namespace_line};

use super::{
    CacheArgs, discard, file_mode_context, locate_project, new_session, report, unchecked_summary,
    use_cache,
};

/// What `doc` was asked.
pub(super) struct Args<'a> {
    pub name: &'a str,
    pub file: Option<&'a Path>,
    /// `--coverage`: the namespaces asked for (none: the default).
    pub coverage: Option<&'a [String]>,
    pub project: Option<&'a Path>,
    pub json: bool,
    /// How many theorems to show; 0: none, and no check.
    pub theorems: usize,
    pub cache: &'a CacheArgs,
}

/// A file given on the command line, read.
struct FileArg<'a> {
    path: &'a Path,
    text: String,
}

/// The program `doc` looks in.
struct Program {
    name: String,
    dir: PathBuf,
    analysis: Analysis,
}

pub(super) fn doc(args: &Args) -> ExitCode {
    let mut session = new_session(false);
    let explicit = args.project.is_some() || args.file.is_some();
    // What the name may be: the library, and the file or the project.
    let mut file: Option<FileArg> = None;
    let mut program: Option<Program> = None;
    let mut inputs: Vec<Input> = Vec::new();
    match args.file {
        Some(path) => {
            let text = match std::fs::read_to_string(path) {
                Ok(text) => text,
                Err(err) => {
                    eprintln!("error: can't read {}: {err}", path.display());
                    return ExitCode::from(2);
                }
            };
            let mut scratch = SourceMap::new();
            let id = scratch.add(path.display().to_string(), text.as_str());
            inputs.push(Input {
                display: path.display().to_string(),
                text: text.clone(),
                // A file without a `namespace` line is in `Main`.
                namespace: Some(
                    parse_namespace_line(id, &text)
                        .ok()
                        .flatten()
                        .map_or_else(|| "Main".to_string(), |line| line.path.text),
                ),
            });
            use_cache(&mut session, args.cache, Path::new("."));
            file = Some(FileArg { path, text });
        }
        None => {
            let found = match args.project {
                Some(_) => locate_project(args.project, "document", "doc NAME hello.sw"),
                None => {
                    let cwd = std::env::current_dir().unwrap_or_else(|_| PathBuf::from("."));
                    project::find_project(&cwd)
                        .and_then(|dir| locate_project(Some(&dir), "document", ""))
                }
            };
            match found {
                Some(found) => {
                    use_cache(&mut session, args.cache, &found.dir);
                    let files = DiskFiles {
                        root: found.dir.clone(),
                    };
                    let read = project_sources(&files, &found.name, &mut session.sources);
                    let analysis = read.map(|sources| analyse(&mut session, &found.name, sources));
                    match analysis {
                        Ok(analysis) if analysis.diagnostics.is_empty() => {
                            for ns in &analysis.namespaces {
                                for &id in &ns.files {
                                    let f = session.sources.get(id);
                                    inputs.push(Input {
                                        display: f.name.clone(),
                                        text: f.text.clone(),
                                        namespace: Some(ns.name.clone()),
                                    });
                                }
                            }
                            program = Some(Program {
                                name: found.name,
                                dir: found.dir,
                                analysis,
                            });
                        }
                        // A project asked for that doesn't read is an error;
                        // one found from the folder is left out.
                        Ok(analysis) if explicit => {
                            report(&session.sources, &analysis.diagnostics);
                            return ExitCode::from(2);
                        }
                        Err(diagnostics) if explicit => {
                            report(&session.sources, &diagnostics);
                            return ExitCode::from(2);
                        }
                        _ => eprintln!(
                            "note: the project in this folder doesn't read: only the library is looked in (`stitchwort check` shows why)"
                        ),
                    }
                }
                None if args.project.is_some() => return ExitCode::from(2),
                None => use_cache(&mut session, args.cache, Path::new(".")),
            }
        }
    }

    let decls = Decls::new(inputs);
    if let Some(names) = args.coverage {
        let code = coverage(&decls, names, program.is_some(), args);
        discard(session);
        return code;
    }
    let resolution = decls.resolve(args.name);
    let code = answer(&mut session, &decls, &resolution, args, file, program);
    discard(session);
    code
}

/// `--coverage` (SW-1025): from parsing alone, never fails for what it
/// finds; a name that isn't a namespace is an error (2).
fn coverage(decls: &Decls, names: &[String], program: bool, args: &Args) -> ExitCode {
    let report = if names.is_empty() {
        decls.default_coverage(program)
    } else {
        let mut found: Vec<String> = Vec::new();
        for name in names {
            let namespaces = decls.resolve(name).namespaces;
            if namespaces.is_empty() {
                eprintln!(
                    "error: `{name}` is not a namespace (`stitchwort doc {name}` shows what it is)"
                );
                return ExitCode::from(2);
            }
            for ns in namespaces {
                if !found.contains(&ns) {
                    found.push(ns);
                }
            }
        }
        decls.coverage(&found)
    };
    emit(args, || render_coverage(&report), &report);
    ExitCode::SUCCESS
}

/// Prints a report as JSON, or as the text made from it.
fn emit<T: Serialize>(args: &Args, text: impl FnOnce() -> String, value: &T) {
    if args.json {
        println!(
            "{}",
            serde_json::to_string(value).expect("a doc report serialises")
        );
    } else {
        print!("{}", text());
    }
}

/// Prints what `name` resolved to, checking what its report needs.
fn answer(
    session: &mut Session,
    decls: &Decls,
    resolution: &Resolution,
    args: &Args,
    file: Option<FileArg>,
    program: Option<Program>,
) -> ExitCode {
    let (entries, namespaces) = (&resolution.entries, &resolution.namespaces);
    if entries.len() > 1 || (entries.is_empty() && namespaces.len() > 1) {
        let matches = Matches {
            version: 1,
            matches: entries.iter().map(|&i| decls.found(i)).collect(),
            namespaces: namespaces.clone(),
            closest: Vec::new(),
        };
        emit(args, || render_matches(args.name, &matches), &matches);
        return ExitCode::from(2);
    }
    let Some(&index) = entries.first() else {
        if let Some(ns) = namespaces.first() {
            let listing = decls.namespace(ns);
            emit(args, || render_namespace(&listing), &listing);
            return ExitCode::SUCCESS;
        }
        let matches = Matches {
            version: 1,
            matches: Vec::new(),
            namespaces: Vec::new(),
            closest: (decls.closest(args.name).into_iter())
                .map(|i| decls.found(i))
                .collect(),
        };
        emit(args, || render_matches(args.name, &matches), &matches);
        return ExitCode::FAILURE;
    };

    // Where examples and theorems are looked for (D2146).
    let entry = decls.entry(index);
    let dependents: Option<Vec<String>> = match (decls.namespace_of(index), &program) {
        (Some(ns), Some(p)) => Some(project::dependents(&p.analysis, ns)),
        _ => None,
    };
    // A library name is looked for in the library alone, unless a project or
    // a file was named on the command line.
    let with_project = args.project.is_some() || args.file.is_some();
    let within = match &dependents {
        Some(names) => Within {
            std: false,
            project: true,
            namespaces: Some(names.iter().cloned().collect::<BTreeSet<_>>()),
        },
        None => Within {
            std: true,
            project: with_project,
            namespaces: None,
        },
    };
    let mut result = decls.report(index, &within);

    // The elaborated type and the theorems need the check (D2152).
    let checkable = !matches!(entry.kind, Kind::Type | Kind::Interface | Kind::Ability);
    if args.theorems > 0 && checkable {
        let mut extra = String::new();
        if let Some(names) = &dependents {
            for ns in names {
                extra.push_str(&format!(" --in {ns}"));
            }
        }
        if let Some(project) = args.project {
            extra.push_str(&format!(" --project {}", project.display()));
        }
        if let Some(file) = &file {
            extra.push_str(&format!(" {}", file.path.display()));
        }
        let loaded = load(
            session,
            file.as_ref(),
            program,
            dependents.as_deref(),
            with_project,
        );
        let scope = match loaded {
            Ok(scope) => scope,
            Err(code) => return code,
        };
        result.ty = session.declared_type(&entry.path);
        if entry.kind == Kind::Definition {
            let names = dependents.clone().unwrap_or_default();
            let bare = (decls.namespace_of(index))
                .and_then(|ns| entry.path.strip_prefix(ns)?.strip_prefix('.'));
            let found =
                session.theorems_about(&entry.path, bare, &names, &scope, args.theorems, &extra);
            match found {
                Ok((theorems, warnings)) => {
                    result.theorems = Some(theorems);
                    result.warnings.extend(warnings);
                }
                Err(d) => result
                    .warnings
                    .push(format!("the theorems couldn't be searched: {}", d.message)),
            }
            match session.equations_of(&entry.path, &extra) {
                Ok(equations) => result.equations = equations,
                Err(d) => result
                    .warnings
                    .push(format!("the equations couldn't be listed: {}", d.message)),
            }
        }
    }
    // A type that is a namespace too: its listing follows.
    if matches!(entry.kind, Kind::Type | Kind::Interface | Kind::Ability)
        && let Some(ns) = namespaces.iter().find(|ns| **ns == entry.path)
    {
        result.namespace = Some(decls.namespace(ns));
    }
    emit(args, || render_text(&result, args.theorems > 0), &result);
    ExitCode::SUCCESS
}

/// Loads the library, and what the program needs: the namespaces of
/// `dependents` (D2146), or all of them when the name is the library's and a
/// project was named, or the file. Returns the scope to search in, or the
/// exit code if it can't be loaded.
fn load(
    session: &mut Session,
    file: Option<&FileArg>,
    program: Option<Program>,
    dependents: Option<&[String]>,
    with_project: bool,
) -> Result<Scope, ExitCode> {
    let scope = if let Some(file) = file {
        let context = file_mode_context(file.path, &file.text, "documented");
        let folder = file
            .path
            .parent()
            .filter(|p| !p.as_os_str().is_empty())
            .unwrap_or(Path::new("."));
        if let Some(name) = file.path.file_name().and_then(|n| n.to_str()) {
            session.include_in_folder(
                std::rc::Rc::new(DiskFiles {
                    root: folder.to_path_buf(),
                }),
                name,
            );
        }
        if let Err(diagnostics) =
            session.load_file(&file.path.display().to_string(), &file.text, context)
        {
            unchecked_summary(&session.sources, &diagnostics, "the file");
        }
        std::mem::take(&mut session.warnings);
        Scope::File
    } else if let Some(program) = program
        && (dependents.is_some() || with_project)
    {
        session.include_from(std::rc::Rc::new(DiskFiles {
            root: program.dir.clone(),
        }));
        let (target, names) = match dependents {
            Some(roots) => (
                Target::Namespaces(roots.to_vec()),
                project::closure(&program.analysis, roots),
            ),
            None => (
                Target::Everything,
                (program.analysis.namespaces.iter())
                    .map(|ns| ns.name.clone())
                    .collect(),
            ),
        };
        match session.load_analysis(&program.name, program.analysis, &target) {
            Ok(_) => {
                std::mem::take(&mut session.warnings);
            }
            Err(diagnostics) => unchecked_summary(&session.sources, &diagnostics, "the project"),
        }
        session.elab.leave_namespace();
        Scope::Project(names)
    } else {
        Scope::Project(Vec::new())
    };
    if let Err(diagnostics) = session.elab.load_all_libraries() {
        report(&session.sources, &diagnostics);
        return Err(ExitCode::from(2));
    }
    Ok(scope)
}
