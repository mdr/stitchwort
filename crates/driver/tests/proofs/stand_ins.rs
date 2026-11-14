//! Stand-ins for declarations with an error
//! (docs/proposals/tests-with-errors.md §3.3): what kind of declaration
//! each is in the kernel.

use stitchwort_driver::driver::{Session, with_stack};

const STACK: usize = 16 * 1024 * 1024;

const SOURCE: &str = "namespace A\n\
    def double (n: Nat): Nat := n + n\n\
    def keep (h: double 2 = 5): Nat := 4\n\
    theorem doubleTwo: double 2 = 5 := rfl\n\
    def broken (n: Nat): Nat := \"oops\"\n\
    theorem ownMistake: keep doubleTwo = 3 := rfl\n";

/// A theorem's stand-in is a theorem, a definition's a definition, so what
/// asks whether a term may be stuck on an open goal (`waits_on_goal`: only
/// definitions compute with one) doesn't take a user's own error beside a
/// broken theorem for one that waits.
#[test]
fn a_theorem_s_stand_in_is_a_theorem_and_a_definition_s_is_not() {
    with_stack(STACK, || {
        let mut session = Session::for_stack(STACK);
        let diagnostics = session.load("a.sw", SOURCE).expect_err("has errors");
        let g = session.elab.ev();
        let stand_in = |path: &str| {
            (g.env.defs().iter())
                .find(|d| d.assumption().is_some_and(|a| a.is_error()) && **d.path() == *path)
                .unwrap_or_else(|| panic!("no stand-in for {path}"))
                .theorem()
        };
        assert!(stand_in("A.doubleTwo"));
        assert!(!stand_in("A.broken"));
        // `ownMistake`'s own error is still its own.
        assert!(
            diagnostics
                .iter()
                .any(|d| d.code == "E-REFL" || d.code == "E-TYPE-MISMATCH"),
            "{diagnostics:?}"
        );
    });
}
