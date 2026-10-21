//! Interfaces and instances (docs/proposals/interfaces.md, stage 1): what
//! the examples can't show. That finding an instance waits where §5.5 says
//! it must (the examples only show the answer it then gets), the step
//! budget (§5.5 step 7, D182), and the `instance` marker in the hash (§9.3).
//! The surface behaviour is in `examples/accept/interfaces*.sw` and the
//! `instance-*` and `interface-*` rejects.

use stitchwort_core::hash::def_hash;
use stitchwort_driver::driver::Session;

/// Loads `source`, with the instance step budget `budget` (`None`: the
/// default): the error codes, and how often finding an instance waited.
fn load(budget: Option<usize>, source: &str) -> (Vec<&'static str>, usize) {
    let mut session = Session::new();
    session.elab.instance_budget = budget;
    let codes = match session.load("test.sw", source) {
        Ok(_) => Vec::new(),
        Err(errors) => errors.iter().map(|e| e.code).collect(),
    };
    (codes, session.elab.instance_waits.get())
}

const PRETTY: &str = "\
interface HasZero (a: Type) =
  { zero: a }

instance HasZero.instNat: HasZero Nat :=
  { zero = 0 }

interface Pretty (a: Type) =
  { pretty: a -> Text }

type W (n: Nat) =
  | MkW

instance W.instPretty: Pretty (W n) :=
  { pretty = w => \"global\" }

def makePretty [auto z: HasZero Nat]: Pretty (W (HasZero.zero [hasZero := z])) :=
  { pretty = w => \"local\" }
";

/// The re-review's example: with `HasZero Nat` found first, the local `o`
/// matches at once; with `Pretty (W 0)` tried first, testing `o` is blocked
/// on the unknown `HasZero Nat`, so it waits, and `o` is chosen then. The
/// tests check `o` is chosen both ways.
#[test]
fn a_candidate_blocked_on_an_unknown_waits() {
    let zero_first = format!(
        "{PRETTY}
def zeroFirst: Text :=
  let o: Pretty (W (HasZero.zero [hasZero := _])) := makePretty
  Pretty.pretty [a := W 0] MkW

test \"zero first\" := zeroFirst == \"local\"
"
    );
    assert_eq!(load(None, &zero_first), (vec![], 0));
    let goal_first = format!(
        "{PRETTY}
def goalFirst: Text :=
  ((o: Pretty (W (HasZero.zero [hasZero := _]))) => Pretty.pretty [a := W 0] MkW) makePretty

test \"goal first\" := goalFirst == \"local\"
"
    );
    assert_eq!(load(None, &goal_first), (vec![], 1));
}

/// Two dictionaries in scope whose values depend on unknowns found later:
/// comparing them waits, then they're merged.
#[test]
fn a_comparison_blocked_on_an_unknown_waits() {
    let source = format!(
        "{PRETTY}
instance Pretty.instNat: Pretty Nat :=
  {{ pretty = n => \"global\" }}

def build [auto z: HasZero Nat]: Pretty Nat :=
  {{ pretty = n => if n == HasZero.zero [hasZero := z] then \"zero\" else \"local\" }}

def same (p: Pretty Nat) (q: Pretty Nat) (e: p = q): Text := \"\"

def mergedLater: Text :=
  let o1: Pretty Nat := build [z := _]
  let o2: Pretty Nat := build [z := _]
  Pretty.pretty 0 ++ same o1 build rfl ++ same o2 build rfl
"
    );
    assert_eq!(load(None, &source), (vec![], 1));
}

/// A dictionary in the head equated with an unknown that has its own
/// obligation isn't a solution: it waits for that one.
#[test]
fn a_head_dictionary_equated_with_an_unknown_waits() {
    let source = "\
interface Ordered (a: Type) =
  { less: a -> a -> Bool }

interface Pretty (a: Type) =
  { pretty: a -> Text }

instance Ordered.instNat: Ordered Nat :=
  { less = m n => Nat.leq (m + 1) n }

instance Pretty.instNat: Pretty Nat :=
  { pretty = n => \"n\" }

type Box (k: Type) (o: Ordered k) =
  | MkBox (item: k)

instance Box.instPretty [auto p: Pretty k]: Pretty (Box k o) :=
  { pretty = b => \"box\" }

def box [auto ord: Ordered k] (x: k): Box k ord := MkBox x

def shown: Text := Pretty.pretty (box 3)
";
    assert_eq!(load(None, source), (vec![], 1));
}

const DEEP: &str = "\
interface Same (a: Type) =
  { same: a -> a -> Bool }

instance Same.instNat: Same Nat :=
  { same = m n => m == n }

instance Same.instList [auto s: Same a]: Same (List a) :=
  { same = xs ys => True }

def deep: List (List (List (List (List (List (List (List (List (List (List (List Nat))))))))))) :=
  []

def check: Bool := Same.same deep deep
";

/// No depth limit: twelve deep is fine. But there is a budget of steps, and
/// running out says resolution stopped, not that there's no instance.
#[test]
fn the_step_budget_stops_resolution() {
    assert_eq!(load(None, DEEP), (vec![], 0));
    assert_eq!(load(Some(5), DEEP).0, vec!["E-INSTANCE-BUDGET"]);
}

/// The budget is for the whole tree of an obligation, across the rounds it
/// waits: retrying doesn't refill it.
#[test]
fn the_budget_lasts_across_retries() {
    // `Pretty (Box Nat ?ord)` waits once (two steps for the round) and
    // then finds its instance and the element's.
    let source = "\
interface Ordered (a: Type) =
  { less: a -> a -> Bool }

interface Pretty (a: Type) =
  { pretty: a -> Text }

instance Ordered.instNat: Ordered Nat :=
  { less = m n => True }

instance Pretty.instNat: Pretty Nat :=
  { pretty = n => \"n\" }

type Box (k: Type) (o: Ordered k) =
  | MkBox (item: k)

instance Box.instPretty [auto p: Pretty k]: Pretty (Box k o) :=
  { pretty = b => \"box\" }

def box [auto ord: Ordered k] (x: k): Box k ord := MkBox x

def shown: Text := Pretty.pretty (box 3)
";
    assert_eq!(load(Some(3), source).0, Vec::<&str>::new());
    assert_eq!(load(Some(2), source).0, vec!["E-INSTANCE-BUDGET"]);
}

/// The `instance` marker is part of a definition's hash; nothing else
/// changes.
#[test]
fn the_instance_marker_is_hashed() {
    let hash = |keyword: &str| {
        let source = format!(
            "interface Pretty (a: Type) =\n  {{ pretty: a -> Text }}\n\n\
             {keyword} Pretty.instNat: Pretty Nat :=\n  {{ pretty = n => \"n\" }}\n"
        );
        let mut session = Session::new();
        session.load("test.sw", &source).expect("loads");
        let id = session.elab.lookup_def("Pretty.instNat").expect("defined");
        def_hash(&session.elab.globals, id)
            .expect("in budget")
            .expect("final")
    };
    assert_ne!(hash("instance"), hash("def"));
}
