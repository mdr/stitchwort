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
