//! Shared by the session test binaries.

use std::sync::Arc;

use serde_json::json;
use stitchwort_lsp::{Inline, Memory, MemoryProject, Options};

/// A project source whose checks replay the standard library from the test
/// std cache (docs/testing.md, "The test std cache") instead of checking it
/// from source in every test. The first test to run writes the entries.
///
/// With the cache empty after a compiler change, every test process would
/// check the library at once, so the first fills it alone (as
/// `Session::eager_for_stack` does) by opening a small file, and the others
/// wait for that and then replay.
pub fn cached_memory(stack: usize) -> Arc<Memory> {
    static FILLED: std::sync::Once = std::sync::Once::new();
    let dir = stitchwort_driver::driver::test_std_cache_dir(stack).join("lsp");
    FILLED.call_once(|| {
        let turn = stitchwort_driver::driver::TestCacheTurn::take(&dir);
        if turn.is_filling() {
            let text = "namespace Demo\n\ndef one: Nat := 1\n";
            let memory = Arc::new(Memory::with_cache(dir.clone()));
            memory.add(MemoryProject {
                root: "/memory/proj".into(),
                sources: vec!["src".into()],
                files: Arc::new([("src/Demo.sw".to_string(), text.to_string())].into()),
            });
            std::thread::Builder::new()
                .stack_size(stack)
                .spawn(move || fill(text, memory, stack))
                .unwrap()
                .join()
                .unwrap();
            turn.finish();
        }
    });
    Arc::new(Memory::with_cache(dir))
}

fn fill(text: &str, memory: Arc<Memory>, stack: usize) {
    let mut server = Inline::new(Options::new(stack), memory).unwrap();
    for message in [
        json!({"jsonrpc": "2.0", "id": 1, "method": "initialize", "params": {"capabilities": {}}}),
        json!({"jsonrpc": "2.0", "method": "initialized", "params": {}}),
        json!({"jsonrpc": "2.0", "method": "textDocument/didOpen", "params": {"textDocument": {
            "uri": "file:///memory/proj/src/Demo.sw", "languageId": "stitchwort", "version": 1, "text": text,
        }}}),
    ] {
        server.receive(&message.to_string());
    }
    while server.tick().1 {}
}
