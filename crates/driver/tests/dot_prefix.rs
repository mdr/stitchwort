//! A call by dot notation elaborates to the same term as its prefix form
//! (SW-129, docs/syntax.md, "Records"): `examples/accept/dot-prefix.sw` has
//! pairs of definitions `xDot` and `xPrefix` with the same hash.

use std::path::Path;

use stitchwort_core::DefId;
use stitchwort_core::hash::def_hash;
use stitchwort_driver::driver::Session;

#[test]
fn dot_calls_have_the_hash_of_their_prefix_forms() {
    let path = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../examples/accept/dot-prefix.sw");
    let text = std::fs::read_to_string(&path).unwrap();
    let mut session = Session::eager();
    if let Err(errors) = session.load(&path.display().to_string(), &text) {
        panic!("{errors:#?}");
    }
    let g = &session.elab.globals;
    let _op = g.budget.operation(stitchwort_core::Limits::default());
    let hash = |name: &str| {
        let id = (0..g.defs.len())
            .map(DefId)
            .find(|d| &*g.def(*d).path == name)
            .unwrap_or_else(|| panic!("no `{name}`"));
        def_hash(g, id).unwrap().unwrap().hex()
    };
    let mut pairs = 0;
    for i in 0..g.defs.len() {
        let path = &*g.defs[i].path;
        if let Some(stem) = path.strip_suffix("Dot") {
            assert_eq!(
                hash(path),
                hash(&format!("{stem}Prefix")),
                "`{path}` elaborates differently from its prefix form"
            );
            pairs += 1;
        }
    }
    assert!(pairs >= 6, "only {pairs} pairs found");
}

/// A long chain of dot calls, each receiver itself a dot call, is checked in
/// time linear in its length. Each level once inferred its receiver twice
/// (and the parser computed a chain's span twice per field), so these took
/// time exponential in the length and never finished.
#[test]
fn long_dot_chains_are_cheap() {
    let chain = |n: usize, end: &str| {
        format!(
            "def xs: List Nat := [1, 2, 3]\ndef r: List Nat := xs{}{end}\n",
            ".reverse".repeat(n)
        )
    };
    let mut ok = Session::new();
    assert!(ok.load("chain.sw", &chain(60, "")).is_ok());
    // A failing last call, and a failing first one: each tried the prefix
    // form and then the dot reading again at every level.
    let mut bad = Session::new();
    assert!(bad.load("bad.sw", &chain(60, ".take \"a\"")).is_err());
    let mut inner = Session::new();
    let source = format!(
        "def xs: List Nat := [1, 2, 3]\ndef r: List Nat := xs.nope{}\n",
        ".reverse".repeat(60)
    );
    assert!(inner.load("inner.sw", &source).is_err());
}
