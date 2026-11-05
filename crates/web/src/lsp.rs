//! The language server in the editor's worker (`stitchwort-lsp`'s
//! [`Inline`](stitchwort_lsp::Inline)), driven without threads or standard
//! input and output. The worker hands it each JSON-RPC message from the
//! editor and, while it says there is more to do, calls `tick` between
//! messages; both answer with the messages the server sent, as a JSON array.

use std::sync::Arc;

use stitchwort_lsp::{Memory, MemoryProject};
use wasm_bindgen::prelude::wasm_bindgen;

#[wasm_bindgen]
pub struct LanguageServer {
    inner: stitchwort_lsp::Inline,
    /// The projects the page has given it.
    projects: Arc<Memory>,
}

#[wasm_bindgen]
impl LanguageServer {
    /// A server; call after `load_std`.
    #[wasm_bindgen(constructor)]
    pub fn new() -> Result<LanguageServer, String> {
        let projects = Arc::new(Memory::default());
        Ok(LanguageServer {
            inner: stitchwort_lsp::Inline::new(options(), projects.clone())?,
            projects,
        })
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
}

#[wasm_bindgen]
impl SearchWorker {
    /// A search worker; call after `load_std`.
    #[wasm_bindgen(constructor)]
    pub fn new() -> SearchWorker {
        let projects = Arc::new(Memory::default());
        SearchWorker {
            inner: stitchwort_lsp::Searcher::new(search_options(), projects.clone()),
            projects,
        }
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

    /// Runs the search `job` (a `search` of `take_searches`), and returns
    /// its result as JSON.
    pub fn run(&self, job: &str) -> String {
        self.inner.run(job)
    }
}

impl Default for SearchWorker {
    fn default() -> Self {
        SearchWorker::new()
    }
}

/// The server's options in the worker. `Limits::for_stack` keeps a quarter
/// (at least 256 KiB) in reserve, so the stack given below leaves a guard of
/// half the playground sessions' (`STITCHWORT_GUARD`, 256 KiB). The server
/// checks with its navigation data on, and with the full guard that overflowed
/// V8's own stack (a `RangeError`, after which the instance is unusable) when
/// a file of a namespace others depend on (`Aoc.Common`) was opened in
/// the editor, so it stops such a check with a resource error sooner.
fn options() -> stitchwort_lsp::Options {
    let guard: usize = env!("STITCHWORT_GUARD").parse().unwrap_or(256 * 1024);
    stitchwort_lsp::Options::new(guard / 2 + 256 * 1024)
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
