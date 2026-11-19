//! Shared by the session tests.

use std::sync::Arc;

use serde_json::{Value, json};
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

/// A program whose or-patterns bind `size` (two alternatives, then three)
/// and a proof whose `same` has a different type in each alternative
/// (SW-4250, D3694).
pub const OR_BINDING: &str = "namespace Demo

type Shape = | Circle (radius: Nat) | Square (side: Nat) | Dot (r: Nat)

def size: Shape → Nat
  | Circle size | Square size => size + 1
  | Dot _ => 0

def three: Shape → Nat
  | Circle n | Square n | Dot n => n + 1

def level (text: Text): Nat := if text == \"&&\" || text == \"∧\" then 5 else 4

theorem andLevel ∀ (text: Text)
    (spelt: text = \"&&\" ∨ text = \"∧\")
    : level text = 5 :=
  match spelt with
    | Inl same | Inr same => rewrite same
";

/// The position `delta` characters into the `nth` `needle` of `text`.
pub fn position_in(text: &str, needle: &str, nth: usize, delta: usize) -> Value {
    let start = text.match_indices(needle).nth(nth).expect("in the text").0 + delta;
    let before = &text[..start];
    let line = before.matches('\n').count();
    let character = before.rsplit('\n').next().unwrap_or("").chars().count();
    json!({"line": line, "character": character})
}

pub fn locations(found: &Value) -> Vec<(u64, u64)> {
    let list: Vec<&Value> = match found {
        Value::Array(items) => items.iter().collect(),
        Value::Null => Vec::new(),
        one => vec![one],
    };
    let mut out: Vec<(u64, u64)> = list
        .iter()
        .map(|l| {
            let start = &l["range"]["start"];
            (
                start["line"].as_u64().unwrap(),
                start["character"].as_u64().unwrap(),
            )
        })
        .collect();
    out.sort();
    out
}

/// Where `needle`'s `nth` occurrence starts, as (line, character).
pub fn start_of(text: &str, needle: &str, nth: usize) -> (u64, u64) {
    let p = position_in(text, needle, nth, 0);
    (
        p["line"].as_u64().unwrap(),
        p["character"].as_u64().unwrap(),
    )
}

/// The binder `name` inside the `nth` `alternative` text, as (line, character).
pub fn binder_in(alternative: &str, name: &str) -> (u64, u64) {
    let (line, character) = start_of(OR_BINDING, alternative, 0);
    (line, character + alternative.find(name).unwrap() as u64)
}

/// The three kinds of name: two alternatives in a program, three, and the
/// proof's, each with its use in the body.
/// A use's snippet, its name, and the name's bindings in order.
pub type OrName = (&'static str, &'static str, Vec<(u64, u64)>);

pub fn or_names() -> Vec<OrName> {
    vec![
        (
            "size + 1",
            "size",
            vec![
                binder_in("Circle size", "size"),
                binder_in("Square size", "size"),
            ],
        ),
        (
            "n + 1",
            "n",
            vec![
                binder_in("Circle n |", "n"),
                binder_in("Square n |", "n"),
                binder_in("Dot n =>", "n"),
            ],
        ),
        (
            "rewrite same",
            "same",
            vec![binder_in("Inl same", "same"), binder_in("Inr same", "same")],
        ),
    ]
}

/// Where the use `use_of` (a snippet starting at or before the name) has `name`.
pub fn use_at(use_of: &str, name: &str) -> (u64, u64) {
    let (line, character) = start_of(OR_BINDING, use_of, 0);
    (line, character + use_of.find(name).unwrap() as u64)
}
