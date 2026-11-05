//! The language server in the worker (SW-1375 trial): the native server's
//! own code (`crates/cli/src/lsp.rs`), driven without threads or standard
//! input and output. The worker hands it each JSON-RPC message from the
//! editor and, while it says there is more to do, calls `tick` between
//! messages; both answer with the messages the server sent, as a JSON array.

use wasm_bindgen::prelude::wasm_bindgen;

#[path = "../../cli/src/lsp.rs"]
#[allow(dead_code, unused_imports)]
mod server;

#[wasm_bindgen]
pub struct LanguageServer {
    inner: server::Inline,
}

#[wasm_bindgen]
impl LanguageServer {
    /// A server; call after `load_std`.
    #[wasm_bindgen(constructor)]
    pub fn new() -> Result<LanguageServer, String> {
        // `Limits::for_stack` keeps a quarter (at least 256 KiB) in reserve:
        // this leaves the guard the playground's sessions use.
        let guard: usize = env!("STITCHWORT_GUARD").parse().unwrap_or(256 * 1024);
        let options = server::Options::new(guard + 256 * 1024);
        Ok(LanguageServer {
            inner: server::Inline::new(options)?,
        })
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
}

fn array(messages: Vec<String>) -> String {
    format!("[{}]", messages.join(","))
}
