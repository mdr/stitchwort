//! Every binding by content hash applies to the library as it is.
//!
//! Natives, native representations and kernel rules are bound to library
//! declarations by content hash (DESIGN.md §11): `R3`/`R4` of `+`
//! (`stitchwort_core::nat_add`), compact text (`chars`), `Float` and its
//! kernel natives (`float`), and the runtimes' representations and natives
//! (`stitchwort_rt::natives`). A binding whose declaration changed is
//! dropped without a word, by design: the declaration then runs as written,
//! slower but right. So a library change can switch a native off silently:
//! changing `Nat.divFuel` (SW-922) unbound `Nat.toText`'s and eight `Int`
//! natives in the runtimes, and only a JS snapshot and an allocation count
//! showed it. This test makes it loud: every binding must apply after the
//! whole library has loaded, and every hash pinned in the compiler's source
//! must be one this test checked, so a new pin can't be left out of it.
//!
//! When it fails after a library change, check each native or rule it names
//! against the changed declaration (that it still computes what the
//! declaration does), then update the pinned hash to the one printed.

use std::collections::BTreeSet;
use std::path::{Path, PathBuf};

use stitchwort_core::registry::Builtin;
use stitchwort_core::{DataId, Globals, chars, float, nat_add};
use stitchwort_driver::driver::{Session, with_session};
use stitchwort_rt::natives;

const STACK: usize = 64 * 1024 * 1024;

fn data(g: &Globals, name: &str) -> DataId {
    g.find_data(name)
        .unwrap_or_else(|| panic!("the prelude defines `{name}`"))
}

/// Each binding by content hash: its name, the hash its declaration has now,
/// and whether that is the pinned one.
fn bindings(g: &Globals) -> Vec<(String, Option<String>, bool)> {
    let mut out = Vec::new();
    // R3 and R4 of `+`: off unless `Nat.add` is the pinned declaration.
    let add = nat_add::add_hash(g);
    let on = add.as_deref() == Some(nat_add::NAT_ADD_HASH) && g.builtins.nat_add_rule.is_some();
    out.push(("Nat.add (R3, R4)".to_string(), add, on));
    // Compact text.
    let text = chars::binding(g, data(g, "List"), data(g, "Char"));
    let on = text.bound && g.builtins.text.is_some();
    out.push(("List (compact text)".to_string(), text.list_hash, on));
    out.push(("Char (compact text)".to_string(), text.char_hash, on));
    // `Float` and its kernel natives; a mismatch refuses the library, so
    // this is a second line.
    for (name, hash, pinned) in float::bindings(g) {
        let on = hash.as_deref() == Some(pinned);
        out.push((format!("{name} (kernel)"), hash, on));
    }
    // The runtimes' representations and natives.
    let rt =
        |name: &str, hash: Option<String>, bound: bool| (format!("{name} (runtimes)"), hash, bound);
    let int = natives::bind_int(g).expect("hashes");
    out.push(rt("Int", int.hash, int.bound));
    for b in int.natives {
        out.push(rt(b.name, b.hash, b.bound));
    }
    for b in natives::bind_text_natives(g).expect("hashes") {
        out.push(rt(b.name, b.hash, b.bound));
    }
    for b in natives::bind_float_natives(g).expect("hashes") {
        out.push(rt(b.name, b.hash, b.bound));
    }
    for (name, builtin, pinned, found) in [
        (
            "Nat",
            Builtin::Nat,
            natives::NAT_DATA_HASH,
            natives::nat_data(g),
        ),
        (
            "Text",
            Builtin::Text,
            natives::TEXT_DATA_HASH,
            natives::text_data(g),
        ),
        (
            "SafeNat",
            Builtin::SafeNat,
            natives::SAFE_NAT_HASH,
            natives::safe_nat_data(g),
        ),
        (
            "SafeInt",
            Builtin::SafeInt,
            natives::SAFE_INT_HASH,
            natives::safe_int_data(g),
        ),
    ] {
        let d = g
            .registry
            .loaded_data(builtin)
            .unwrap_or_else(|| panic!("the library declares `{name}`"));
        let hash = {
            let _op = g.budget.operation(stitchwort_core::Limits::stack_only(
                stitchwort_core::Limits::default().stack,
            ));
            stitchwort_core::hash::data_hash(g, d)
                .expect("hashes")
                .map(|h| h.hex())
        };
        let bound = hash.as_deref() == Some(pinned) && found == Some(d);
        out.push(rt(name, hash, bound));
    }
    match natives::float_data(g) {
        Some(_) => {}
        None => out.push(rt("Float", None, false)),
    }
    out
}

/// The `src` folder of every crate.
fn sources() -> Vec<PathBuf> {
    let crates = Path::new(env!("CARGO_MANIFEST_DIR")).join("..");
    let mut files = Vec::new();
    let mut dirs: Vec<PathBuf> = std::fs::read_dir(&crates)
        .expect("crates/")
        .map(|e| e.expect("entry").path().join("src"))
        .filter(|p| p.is_dir())
        .collect();
    while let Some(dir) = dirs.pop() {
        for entry in std::fs::read_dir(&dir).expect("a source folder") {
            let path = entry.expect("entry").path();
            if path.is_dir() {
                dirs.push(path);
            } else if path.extension().is_some_and(|e| e == "rs") {
                files.push(path);
            }
        }
    }
    files.sort();
    files
}

/// The string literals of 64 hex digits in `text`: pinned content hashes.
fn pinned_in(text: &str) -> Vec<String> {
    let bytes = text.as_bytes();
    let mut out = Vec::new();
    for (i, _) in text.match_indices('"') {
        let hex = &bytes[i + 1..];
        if hex.len() > 64
            && hex[64] == b'"'
            && hex[..64]
                .iter()
                .all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(b))
        {
            out.push(text[i + 1..i + 65].to_string());
        }
    }
    out
}

#[test]
fn every_binding_by_hash_applies_to_the_library() {
    let found = with_session(STACK, Session::eager_from_source_for_stack, |session| {
        bindings(&session.elab.globals)
    });
    let unbound: Vec<String> = found
        .iter()
        .filter(|(_, _, bound)| !bound)
        .map(|(name, hash, _)| format!("{name}: now {hash:?}"))
        .collect();
    assert!(
        unbound.is_empty(),
        "these bindings by content hash no longer apply, so their natives or rules are \
         silently off; check each against its changed declaration, then pin the new hash:\n{}",
        unbound.join("\n")
    );
    // Every hash pinned in the source is one checked above.
    let checked: BTreeSet<&str> = found.iter().filter_map(|(_, h, _)| h.as_deref()).collect();
    let mut unchecked = Vec::new();
    for file in sources() {
        let text = std::fs::read_to_string(&file).expect("a source file");
        for hash in pinned_in(&text) {
            if !checked.contains(hash.as_str()) {
                unchecked.push(format!("{}: {hash}", file.display()));
            }
        }
    }
    assert!(
        unchecked.is_empty(),
        "hashes pinned in the source that this test doesn't check; add their bindings to \
         `bindings` in crates/driver/tests/pinned_hashes.rs:\n{}",
        unchecked.join("\n")
    );
}

/// The scan finds a pin written on its own line, as long constants are.
#[test]
fn the_scan_finds_pinned_hashes() {
    let pin = "a".repeat(64);
    let text = format!(
        "const X: &str =\n    \"{pin}\";\nlet y = \"{}\";",
        "b".repeat(65)
    );
    assert_eq!(pinned_in(&text), vec![pin]);
}
