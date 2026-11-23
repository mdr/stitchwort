//! A theorem is referred to by its statement's hash, its *interface* hash
//! (docs/proposals/sealed-theorems.md §3.8, stage 2): editing a proof
//! changes the theorem's own full hash and no other declaration's, while a
//! changed statement, an open goal or an error in the proof still reaches
//! everything that uses it.

use stitchwort_core::DefId;
use stitchwort_core::hash::{def_hash, interface_hash};
use stitchwort_driver::driver::{Cache, Session, with_stack};

const STACK: usize = 16 * 1024 * 1024;

/// `t`'s statement and proof, and its users: a definition, a theorem and a
/// test that pass it as a proof argument.
fn source(statement: &str, proof: &str) -> String {
    format!(
        "namespace A\n\
         def keep (h: {statement}): Nat := 4\n\
         theorem t: {statement} := {proof}\n\
         def k: Nat := keep t\n\
         theorem u: keep t = 4 := byComputing\n\
         test \"k\" := k == 4\n"
    )
}

const USERS: [&str; 3] = ["A.k", "A.u", "A.test \"k\""];

struct Loaded {
    session: Session,
    /// Whether it loaded without errors.
    ok: bool,
}

impl Loaded {
    fn new(text: &str) -> Self {
        let mut session = Session::for_stack(STACK);
        let ok = session.load("a.sw", text).is_ok();
        Loaded { session, ok }
    }

    /// The checked definition at `path`, not a stand-in for one.
    fn id(&self, path: &str) -> DefId {
        let g = self.session.elab.ev();
        (0..g.env.defs().len())
            .map(DefId)
            .rfind(|&d| &**g.def(d).path() == path)
            .unwrap_or_else(|| panic!("no `{path}`"))
    }

    fn hash(&self, path: &str) -> String {
        let g = &self.session.elab.ev();
        let _op = g
            .machine
            .budget
            .operation(stitchwort_core::Limits::default());
        def_hash(g, self.id(path)).unwrap().expect("final").hex()
    }

    fn interface(&self, path: &str) -> String {
        let g = &self.session.elab.ev();
        let _op = g
            .machine
            .budget
            .operation(stitchwort_core::Limits::default());
        interface_hash(g, self.id(path))
            .unwrap()
            .expect("final")
            .hex()
    }

    fn users(&self) -> Vec<String> {
        USERS.iter().map(|u| self.hash(u)).collect()
    }
}

#[test]
fn editing_a_proof_changes_the_theorem_s_full_hash_and_no_user_s() {
    with_stack(STACK, || {
        let direct = Loaded::new(&source("2 + 2 = 4", "byComputing"));
        let flipped = Loaded::new(&source("2 + 2 = 4", "(byComputing: 4 = 2 + 2).flipped"));
        assert_ne!(direct.hash("A.t"), flipped.hash("A.t"), "the full hash");
        assert_eq!(direct.interface("A.t"), flipped.interface("A.t"));
        assert_eq!(direct.users(), flipped.users());
        // A definition's interface hash is its hash.
        assert_eq!(direct.interface("A.k"), direct.hash("A.k"));
    });
}

#[test]
fn changing_a_statement_changes_every_user_s_hash() {
    with_stack(STACK, || {
        let four = Loaded::new(&source("2 + 2 = 4", "byComputing"));
        let five = Loaded::new(&source("2 + 3 = 5", "byComputing"));
        assert_ne!(four.interface("A.t"), five.interface("A.t"));
        for (a, b) in four.users().iter().zip(five.users()) {
            assert_ne!(*a, b);
        }
    });
}

/// A proof with an error is replaced by a stand-in, whose hash is tagged as
/// one, so every user's hash changes.
#[test]
fn a_proof_with_an_error_changes_every_user_s_hash() {
    with_stack(STACK, || {
        let fine = Loaded::new(&source("2 + 2 = 4", "byComputing"));
        let broken = Loaded::new(&source("2 + 2 = 4", "Nat.addZero 3"));
        assert!(fine.ok);
        assert!(!broken.ok, "the broken proof has an error");
        for (a, b) in fine.users().iter().zip(broken.users()) {
            assert_ne!(*a, b);
        }
    });
}

/// An open goal in a proof leaves its users' hashes alone, so what relies
/// on it is found by walking bodies, and a test's cached result is keyed by
/// the goals it relies on too: the result cached while the proof was
/// finished isn't used for the test that now relies on a goal.
#[test]
fn an_open_goal_in_a_proof_reaches_its_users_through_reliance() {
    with_stack(STACK, || {
        let fine = Loaded::new(&source("2 + 2 = 4", "byComputing"));
        let open = Loaded::new(&source("2 + 2 = 4", "?"));
        assert_eq!(fine.users(), open.users());
        assert!(!fine.session.elab.relies_on_goal(fine.id("A.k")));
        assert!(open.session.elab.relies_on_goal(open.id("A.k")));

        let seen = |results: &[stitchwort_driver::driver::TestResult]| {
            (results.iter())
                .map(|r| (r.name.clone(), r.cached, r.assuming.len()))
                .collect::<Vec<_>>()
        };
        let cache = Cache::memory([]);
        let first = fine.session.run_tests(&cache);
        assert!(first.iter().all(|r| !r.cached), "{:?}", seen(&first));
        let again = fine.session.run_tests(&cache);
        assert!(again.iter().all(|r| r.cached), "{:?}", seen(&again));
        let relying = open.session.run_tests(&cache);
        assert!(relying.iter().all(|r| !r.cached), "{:?}", seen(&relying));
        assert!(
            relying.iter().all(|r| !r.assuming.is_empty()),
            "{:?}",
            seen(&relying)
        );
    });
}
