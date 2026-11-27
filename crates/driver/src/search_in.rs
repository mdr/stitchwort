//! A search by type from a file being edited (docs/proposals/editor-type-search.md,
//! stage 1): the query means what it would mean written in the file, and
//! each result's import line is the one the file needs. For the language
//! server's `stitchwort/search`.

use std::sync::atomic::Ordering;

use stitchwort_syntax::Diagnostic;

use crate::driver::Session;
use crate::project::Files;
use crate::rewind::Cancelled;
use crate::search::{Options, Report, Scope};

/// What a search from a file gave: a report, an error in the query (it
/// doesn't parse or elaborate), or nothing because it was cancelled.
pub type Searched = Result<Result<Report, Diagnostic>, Cancelled>;

impl Session {
    /// Searches for `query` from `text`, a file on its own named `name`,
    /// loaded into this session (a fresh one) first. A file that doesn't
    /// check is still searched: its declarations that checked, with its
    /// namespace and imports.
    pub fn search_in_text(
        &mut self,
        name: &str,
        text: &str,
        query: &str,
        options: &Options,
    ) -> Searched {
        if self.cancel_flag().load(Ordering::Relaxed) {
            return Err(Cancelled);
        }
        let _ = self.load(name, text);
        self.warnings.clear();
        if let Err(diagnostics) = self.elab.load_all_libraries() {
            return Ok(Err(first(diagnostics, "the library didn't load")));
        }
        self.search_cancellable(query, options, &Scope::File)
    }

    /// Searches for `query` from the file `path` of the project `project`
    /// (by its path within the project), with the files' text from `files`
    /// (the editor's laid over the disk's). The session loads the library,
    /// then what the file's namespace uses and that namespace, through the
    /// check cache `cache` if given, and stays in the file's scope; so the
    /// project's namespaces the file doesn't use, directly or not, aren't
    /// searched (loading them costs seconds in a big project, at every
    /// query).
    pub fn search_in_project(
        &mut self,
        project: &str,
        files: &dyn Files,
        path: &str,
        cache: Option<&std::path::Path>,
        query: &str,
        options: &Options,
    ) -> Searched {
        if self.cancel_flag().load(Ordering::Relaxed) {
            return Err(Cancelled);
        }
        let fail = |message: String| Ok(Err(Diagnostic::error("E-SEARCH-FILE", message)));
        if let Some(dir) = cache {
            self.use_check_cache(dir);
        }
        if let Some(include) = files.include_files() {
            self.include_from(include);
        }
        if !self.load_libraries_for_probes() {
            return fail("the library didn't load".into());
        }
        let sources = match crate::project::project_sources(files, project, &mut self.sources) {
            Ok(sources) => sources,
            Err(ds) => return Ok(Err(first(ds, "the project can't be read"))),
        };
        if !sources.iter().any(|(p, _)| p == path) {
            return fail(format!("{path} isn't one of the project's source files"));
        }
        let parsed = crate::project::parse_files(self, project, sources);
        let Some(file) = parsed.iter().find(|f| f.path == path).map(|f| f.id) else {
            return fail(format!("{path} didn't parse"));
        };
        let analysis = crate::project::analyse_parsed(&mut self.elab, project, parsed);
        let Some(own) = (analysis.namespaces.iter())
            .find(|n| n.files.contains(&file))
            .map(|n| n.name.clone())
        else {
            return Ok(Err(first(
                analysis.diagnostics,
                "the file has no namespace",
            )));
        };
        let namespaces = analysis.namespaces.iter().map(|n| n.name.clone()).collect();
        // A namespace that doesn't check is searched as it stands.
        if let Err(ds) = self.load_for_probe(project, &analysis, &own) {
            return Ok(Err(first(ds, "the project can't be checked")));
        }
        self.warnings.clear();
        self.elab.use_file_scope(file);
        self.search_cancellable(query, options, &Scope::ProjectFile { namespaces, own })
    }

    /// [`Session::search`], stopped part way when the session's cancel flag
    /// is set: the search checks it between candidates. Not cleared first,
    /// as [`Session::cancellable`] would: the flag is this search's own, and
    /// one set already is a cancellation that came while the file loaded.
    fn search_cancellable(&mut self, query: &str, options: &Options, scope: &Scope) -> Searched {
        if self.cancel_flag().load(Ordering::Relaxed) {
            return Err(Cancelled);
        }
        let mark = self.mark();
        let budget = &self.elab.kernel.machine.budget;
        budget.watch_cancel(true);
        let found = self.search(query, options, scope);
        let budget = &self.elab.kernel.machine.budget;
        budget.watch_cancel(false);
        let cancelled = budget.cancelled();
        if cancelled {
            self.rewind(&mark);
        }
        self.release(mark);
        if cancelled { Err(Cancelled) } else { Ok(found) }
    }
}

/// The first error among `diagnostics`, or one saying `otherwise`.
fn first(diagnostics: Vec<Diagnostic>, otherwise: &str) -> Diagnostic {
    (diagnostics.into_iter())
        .find(|d| d.severity == stitchwort_syntax::Severity::Error)
        .unwrap_or_else(|| Diagnostic::error("E-SEARCH-FILE", otherwise.to_string()))
}
