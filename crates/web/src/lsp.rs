//! The language server in the editor's worker (`stitchwort-lsp`'s
//! [`Inline`](stitchwort_lsp::Inline)), driven without threads or standard
//! input and output. The worker hands it each JSON-RPC message from the
//! editor and, while it says there is more to do, calls `tick` between
//! messages; both answer with the messages the server sent, as a JSON array.

use std::sync::{Arc, OnceLock};

use stitchwort_driver::check_cache::LibraryBundle;
use stitchwort_lsp::{Memory, MemoryProject};
use wasm_bindgen::prelude::wasm_bindgen;

#[wasm_bindgen]
pub struct LanguageServer {
    inner: stitchwort_lsp::Inline,
    /// The projects the page has given it.
    projects: Arc<Memory>,
    /// The server's [`Options::library`](stitchwort_lsp::Options::library).
    library: Arc<OnceLock<Arc<LibraryBundle>>>,
}

#[wasm_bindgen]
impl LanguageServer {
    /// A server; call after `load_std`.
    #[wasm_bindgen(constructor)]
    pub fn new() -> Result<LanguageServer, String> {
        let projects = Arc::new(Memory::default());
        let options = options();
        let library = options.library.clone();
        Ok(LanguageServer {
            inner: stitchwort_lsp::Inline::new(options, projects.clone())?,
            projects,
            library,
        })
    }

    /// Reads the standard library's check cache (`pkg/std.cache.gz`, decompressed by the worker; made by
    /// [`build_library_cache`] when the page was built). The projects and
    /// files loaded after it replay the library files instead of checking
    /// them, so a project's first check takes seconds, not tens of them.
    /// `false` if the bytes aren't a cache this build made (from another
    /// build, say), or one was read already: the library is then checked as
    /// before.
    pub fn load_library_cache(&self, bytes: &[u8]) -> bool {
        LibraryBundle::decode(bytes).is_some_and(|b| self.library.set(Arc::new(b)).is_ok())
    }

    /// Adds the project in folder `root` (`/playground/aoc`), whose
    /// `stitchwort.yaml` lists the source folders `sources`: its files are
    /// `paths` (within the project) and `texts`, the sources and the files
    /// `include` reads. A document opened as `file:///playground/aoc/src/…`
    /// is then checked as a file of the project.
    pub fn add_project(
        &mut self,
        root: &str,
        sources: Vec<String>,
        paths: Vec<String>,
        texts: Vec<String>,
    ) {
        self.projects
            .add(memory_project(root, sources, paths, texts));
    }

    /// The file `path` of the project in `root` has this text, changed by
    /// the page (a rename edited a file the editor hasn't opened).
    pub fn set_project_file(&mut self, root: &str, path: &str, text: String) {
        self.projects
            .set_file(std::path::Path::new(root), path, text);
    }

    /// Handles one message from the client: what the server sent at once.
    pub fn receive(&mut self, message: &str) -> String {
        array(self.inner.receive(message))
    }

    /// The next piece of background work: `{"sent": [...], "more": bool}`.
    pub fn tick(&mut self) -> String {
        let (sent, more) = self.inner.tick();
        format!(r#"{{"sent":{},"more":{more}}}"#, array(sent))
    }

    /// Stops a check whenever `globalThis.stitchwortEditsWaiting()` says
    /// that the page has sent an edit the worker hasn't read yet: the
    /// worker's shared counter (lsp-worker.js). For the whole instance.
    pub fn watch_edits(&self) {
        stitchwort_core::budget::Budget::set_cancel_hook(edits_waiting);
    }

    /// The proof searches queued, for the search worker: a JSON array of
    /// `{"id", "search"}`. Those not taken run in `tick`.
    pub fn take_searches(&mut self) -> String {
        array(self.inner.take_searches())
    }

    /// A search's result from the search worker (`id` as JSON): what the
    /// server sent.
    pub fn searched(&mut self, id: &str, result: &str) -> String {
        array(self.inner.searched(id, result))
    }
}

/// The search worker's end: runs the proof searches the language server
/// hands out, over the same projects.
#[wasm_bindgen]
pub struct SearchWorker {
    inner: stitchwort_lsp::Searcher,
    projects: Arc<Memory>,
    library: Arc<OnceLock<Arc<LibraryBundle>>>,
}

#[wasm_bindgen]
impl SearchWorker {
    /// A search worker; call after `load_std`.
    #[wasm_bindgen(constructor)]
    pub fn new() -> SearchWorker {
        let projects = Arc::new(Memory::default());
        let options = search_options();
        let library = options.library.clone();
        SearchWorker {
            inner: stitchwort_lsp::Searcher::new(options, projects.clone()),
            projects,
            library,
        }
    }

    /// As [`LanguageServer::load_library_cache`]: the searches then replay
    /// the library instead of checking it again.
    pub fn load_library_cache(&self, bytes: &[u8]) -> bool {
        LibraryBundle::decode(bytes).is_some_and(|b| self.library.set(Arc::new(b)).is_ok())
    }

    /// As [`LanguageServer::add_project`].
    pub fn add_project(
        &mut self,
        root: &str,
        sources: Vec<String>,
        paths: Vec<String>,
        texts: Vec<String>,
    ) {
        self.projects
            .add(memory_project(root, sources, paths, texts));
    }

    /// As [`LanguageServer::set_project_file`].
    pub fn set_project_file(&mut self, root: &str, path: &str, text: String) {
        self.projects
            .set_file(std::path::Path::new(root), path, text);
    }

    /// Runs the search `job` (a `search` of `take_searches`), and returns
    /// its result as JSON.
    pub fn run(&self, job: &str) -> String {
        self.inner.run(job)
    }

    /// Loads the library the searches replay, so the first doesn't wait for
    /// it (`stitchwort_lsp::Searcher::warm`).
    pub fn warm(&self) {
        self.inner.warm();
    }
}

impl Default for SearchWorker {
    fn default() -> Self {
        SearchWorker::new()
    }
}

/// Checks the standard library as the language server's projects load it
/// in the worker and returns its check cache, for `pkg/std.cache.gz`
/// (`web/bundle-std-cache.mjs`, from `web/build.sh`). Call after
/// `load_std`. Fails if the cache doesn't load back; `describe_library_cache`
/// says what it holds.
#[wasm_bindgen]
pub fn build_library_cache() -> Result<Vec<u8>, String> {
    stitchwort_lsp::library_bundle(&options()).map(|(bytes, _)| bytes)
}

/// What the library cache in `bytes` holds, for the build's log.
#[wasm_bindgen]
pub fn describe_library_cache(bytes: &[u8]) -> String {
    LibraryBundle::decode(bytes).map_or("not a library cache of this build".to_string(), |b| {
        format!("{b:?}")
    })
}

/// The server's options in the worker: the playground sessions' guard
/// (`STITCHWORT_GUARD`, 256 KiB; `Limits::for_stack` keeps a quarter, at
/// least 256 KiB, in reserve), as for searches.
pub(crate) fn options() -> stitchwort_lsp::Options {
    let guard: usize = env!("STITCHWORT_GUARD").parse().unwrap_or(256 * 1024);
    stitchwort_lsp::Options::new(guard + 256 * 1024)
}

/// The search worker's options: proof searches run in a worker of their own,
/// with the playground sessions' guard.
fn search_options() -> stitchwort_lsp::Options {
    let guard: usize = env!("STITCHWORT_GUARD").parse().unwrap_or(256 * 1024);
    stitchwort_lsp::Options::new(guard + 256 * 1024)
}

pub(crate) fn memory_project(
    root: &str,
    sources: Vec<String>,
    paths: Vec<String>,
    texts: Vec<String>,
) -> MemoryProject {
    MemoryProject {
        root: root.into(),
        sources: (sources.iter())
            .map(|s| s.trim_end_matches('/').to_string())
            .collect(),
        files: Arc::new(paths.into_iter().zip(texts).collect()),
    }
}

#[wasm_bindgen]
extern "C" {
    #[wasm_bindgen(js_name = stitchwortEditsWaiting)]
    fn js_edits_waiting() -> bool;
}

fn edits_waiting() -> bool {
    js_edits_waiting()
}

fn array(messages: Vec<String>) -> String {
    format!("[{}]", messages.join(","))
}
