//! Shared by the session tests.

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
            // The two fills write different units of the cache and share
            // nothing else, so they run side by side: a cold run waits for
            // the slower, not for both.
            let searches = dir.clone();
            let spawn = |body: Box<dyn FnOnce() + Send>| {
                std::thread::Builder::new()
                    .stack_size(stack)
                    .spawn(body)
                    .unwrap()
            };
            let checker = spawn(Box::new(move || fill(text, memory, stack)));
            let searcher = spawn(Box::new(move || fill_for_searches(&searches, stack)));
            checker.join().unwrap();
            searcher.join().unwrap();
            turn.finish();
        }
    });
    Arc::new(Memory::with_cache(dir))
}

/// The playground's library bundle, made by [`stitchwort_lsp::library_bundle`]
/// (which checks the whole library, twice) once per build: the bytes are kept
/// in the test std cache's folder, whose marker holds the build's fingerprint,
/// so a change to the compiler makes the next run make the bundle again, and
/// so check that it loads.
pub fn cached_bundle(options: &Options, stack: usize) -> Vec<u8> {
    let dir = stitchwort_driver::driver::test_std_cache_dir(stack).join("lsp-bundle");
    let file = dir.join("std.cache");
    let turn = stitchwort_driver::driver::TestCacheTurn::take(&dir);
    if !turn.is_filling()
        && let Ok(bytes) = std::fs::read(&file)
    {
        return bytes;
    }
    let (bytes, _) = stitchwort_lsp::library_bundle(options).unwrap();
    if turn.is_filling() {
        std::fs::create_dir_all(&dir).unwrap();
        std::fs::write(&file, &bytes).unwrap();
        turn.finish();
    }
    bytes
}

/// Fills the cache with the entries a proof search reads. They are kept
/// apart from the checker's (the unit's name has `+nav`, where the checker
/// records the types of expressions as well), so without this the first
/// search of a test run checks the whole library from source: over a minute
/// in the release profile, and several in the debug one, with every other
/// test that searches waiting for it.
fn fill_for_searches(dir: &std::path::Path, stack: usize) {
    let mut session = stitchwort_driver::driver::Session::for_stack(stack);
    session.use_check_cache(dir);
    assert!(session.load_libraries_for_probes());
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
