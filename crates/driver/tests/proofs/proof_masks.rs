//! The kernel's comparison skips proofs (docs/proposals/proof-irrelevance.md
//! §7.1, §7.2): constructors' proof fields, data types' proof parameters
//! and definitions' inert arguments; the glued-call shortcut and the other
//! shortcuts compare constructors' proof fields (§7.10). Each case is a pair
//! of definitions with the same parameters, `<case>L` and `<case>R`, whose
//! bodies are compared applied to fresh variables, by `value::conv` with
//! gluing on, with the shortcuts disabled and with gluing off, and by
//! `reference::conv`: all four must give the expected answer. These are the
//! kernel's half of §8's tests (the elaborator's unifier gets the same rules
//! separately).

use std::rc::Rc;

use stitchwort_core::value::{Value, conv, eval, set_shortcuts_disabled};
use stitchwort_core::{DefId, Ev, reference};
use stitchwort_driver::driver::Session;

const PROGRAM: &str = r#"
import Std (Bool, Char, Fin, Int, Nat, Unit, Void)

type Box (a: Prop): Type =
  | MkBox (h: a)

def Box.unbox [a: Prop]: Box a → a
  | MkBox h => h

type Tok: Prop =
  | MkTok

def tokNat (t: Tok) (k: Nat): Nat :=
  match t with
    | MkTok => k

type TBox: Type 1 =
  | MkTBox (t: Type)

def choose (t: Type) (n: Nat): Nat :=
  match n with
    | Zero => 0
    | Succ m => m

type R (p: Prop): Type =
  | MkR

type PBox (a: Prop) (h: a): Type =
  | MkPBox

def cast (a: Type) (b: Type) (h: a = b) (x: a): b := J (y e => y) x h

def myAbsurd: Void → Nat
  | ()

def keep (d: Nat) (ok: d ≠ 0): Box (d ≠ 0) := MkBox ok

def g (n: Nat): 0 = 0 → Bool :=
  match n with
    | Zero => h => J (y e => Bool) True h
    | Succ m => g m

opaque def ou [a: Prop] (b: Box a): a := Box.unbox b

def fnEq (n: Nat) (h: Void → Void): (Nat → Nat) = (Nat → Nat) :=
  match n with
    | Zero => rfl
    | Succ m => rfl

def applyAt (f: Nat → Nat) (x: Nat): Nat := f x

def grpA (n: Nat) (h: 0 = 0): Nat :=
  match n with
    | Zero => J (y e => Nat) 0 h
    | Succ m => grpB m h

def grpB (n: Nat) (h: 0 = 0): Nat :=
  match n with
    | Zero => 1
    | Succ m => grpA m h

def quietA (n: Nat) (h: 0 = 0): Nat :=
  match n with
    | Zero => 0
    | Succ m => quietB m h

def quietB (n: Nat) (h: 0 = 0): Nat :=
  match n with
    | Zero => 1
    | Succ m => quietA m h

-- Test 1: a type field is erased but relevant.
def t1L: TBox := MkTBox Nat
def t1R: TBox := MkTBox Bool
-- Test 2: a type argument of a definition is relevant.
def t2L (n: Nat): Nat := choose Nat n
def t2R (n: Nat): Nat := choose Bool n
-- Division is total, so these stand in for `Int.modNat` and `Nat.mod` as they
-- were when §2.1 and test 20 were written: an inert divisor proof.
def safeModNat (x: Int) (d: Nat) (ok: d ≠ 0): Nat := Int.modNat x d
def safeMod (x: Nat) (d: Nat) (ok: d ≠ 0): Nat := Nat.mod x d
-- §2.1: the divisor proof of a stuck `safeModNat` is skipped.
def sameModL (x: Int) (p: 100 ≠ 0) (q: 100 ≠ 0): Nat := safeModNat x 100 p
def sameModR (x: Int) (p: 100 ≠ 0) (q: 100 ≠ 0): Nat := safeModNat x 100 q
-- Test 20 and its partners.
def t20L (x: Int) (y: Int) (p: 100 ≠ 0): Nat := safeModNat x 100 p
def t20R (x: Int) (y: Int) (p: 100 ≠ 0): Nat := safeModNat y 100 p
def t20dL (x: Int) (d: Nat) (p: d ≠ 0) (q: d ≠ 0): Nat := safeModNat x d p
def t20dR (x: Int) (d: Nat) (p: d ≠ 0) (q: d ≠ 0): Nat := safeModNat x d q
def t20nL (x: Nat) (p: 100 ≠ 0) (q: 100 ≠ 0): Nat := safeMod x 100 p
def t20nR (x: Nat) (p: 100 ≠ 0) (q: 100 ≠ 0): Nat := safeMod x 100 q
-- §2.2: a hand-built character is the literal.
def handBuiltL (p: Char.isScalar 97 = True): Char := MkChar 97 p
def handBuiltR (p: Char.isScalar 97 = True): Char := 'a'
-- Test 3, paired: a proof parameter of a data type is skipped, a data one isn't.
def t3L (a: Prop) (p: a) (q: a): Type := PBox a p
def t3R (a: Prop) (p: a) (q: a): Type := PBox a q
-- Test 9: a proposition parameter is relevant.
def t9L: Type := R Unit
def t9R: Type := R Void
-- Test 6's partner and test 19's: the field mask in normal mode.
def boxL (a: Prop) (p: a) (q: a): Box a := MkBox p
def boxR (a: Prop) (p: a) (q: a): Box a := MkBox q
-- Test 19: the shortcut compares the field, so this is different glued too.
def t19L (a: Prop) (p: a) (q: a): a := Box.unbox (MkBox p)
def t19R (a: Prop) (p: a) (q: a): a := Box.unbox (MkBox q)
-- Test 17: `cast` computes with `h`, so it isn't skipped.
def t17L (a: Type) (h: a = a) (x: a): a := cast a a rfl x
def t17R (a: Type) (h: a = a) (x: a): a := cast a a h x
def t17pL (a: Type) (h: a = a) (x: a): a := cast a a rfl x
def t17pR (a: Type) (h: a = a) (x: a): a := x
-- Test 18: `tokNat` takes `t` apart.
def t18L (t: Tok): Nat := tokNat t 0
def t18R (t: Tok): Nat := tokNat MkTok 0
-- Test 21 and its partner.
def t21L (t: Tok) (u: Tok): Nat := tokNat t 0
def t21R (t: Tok) (u: Tok): Nat := tokNat u 0
def t21pL (p: 0 ≠ 0) (q: 0 ≠ 0): Nat := Void.absurd (p rfl)
def t21pR (p: 0 ≠ 0) (q: 0 ≠ 0): Nat := Void.absurd (q rfl)
-- Test 27: comparing by case trees doesn't compare impossible scrutinees.
def t27aL (p: 0 ≠ 0) (q: 0 ≠ 0): Nat := Void.absurd (q rfl)
def t27aR (p: 0 ≠ 0) (q: 0 ≠ 0): Nat := myAbsurd (q rfl)
def t27bL (p: 0 ≠ 0) (q: 0 ≠ 0): Nat := Void.absurd (p rfl)
def t27bR (p: 0 ≠ 0) (q: 0 ≠ 0): Nat := myAbsurd (q rfl)
-- Test 23: a parameter stored in a field isn't inert.
def t23L (d: Nat) (p: d ≠ 0) (q: d ≠ 0): d ≠ 0 := Box.unbox (keep d p)
def t23R (d: Nat) (p: d ≠ 0) (q: d ≠ 0): d ≠ 0 := Box.unbox (keep d q)
def t23pL (d: Nat) (p: d ≠ 0) (q: d ≠ 0): Box (d ≠ 0) := keep d p
def t23pR (d: Nat) (p: d ≠ 0) (q: d ≠ 0): Box (d ≠ 0) := keep d q
-- Test 24: masks stop at the arity.
def t24L (n: Nat) (h: 0 = 0): Bool := g n rfl
def t24R (n: Nat) (h: 0 = 0): Bool := g n h
-- Test 25: a hidden call compares its arguments in shortcut mode.
def t25L (a: Prop) (p: a) (q: a): a := ou (MkBox p)
def t25R (a: Prop) (p: a) (q: a): a := ou (MkBox q)
-- Test 15: no mask after a `J`; the partner is a mask before one.
def t15L (n: Nat) (u: Void → Void): Nat := applyAt (J (y e => y) (x => x) (fnEq n u)) 3
def t15R (n: Nat) (u: Void → Void): Nat := applyAt (J (y e => y) (x => x) (fnEq n u)) 4
def t15pL (n: Nat) (u1: Void → Void) (u2: Void → Void): Nat := applyAt (J (y e => y) (x => x) (fnEq n u1)) 3
def t15pR (n: Nat) (u1: Void → Void) (u2: Void → Void): Nat := applyAt (J (y e => y) (x => x) (fnEq n u2)) 3
-- Test 22: a group clears a mark through the member that passes it on.
def t22L (n: Nat) (h1: 0 = 0) (h2: 0 = 0): Nat := grpB n h1
def t22R (n: Nat) (h1: 0 = 0) (h2: 0 = 0): Nat := grpB n h2
def t22pL (n: Nat) (h1: 0 = 0) (h2: 0 = 0): Nat := quietB n h1
def t22pR (n: Nat) (h1: 0 = 0) (h2: 0 = 0): Nat := quietB n h2
def t22fL (n: Nat) (i: Nat) (h1: i < n) (h2: i < n): Fin n := Fin.ofNatLt n i h1
def t22fR (n: Nat) (i: Nat) (h1: i < n) (h2: i < n): Fin n := Fin.ofNatLt n i h2

-- Test 4: a data field inside a proof is compared.
type Exists (p: Nat → Prop): Prop =
  | MkEx (x: Nat) (h: p x)
def t4L (h1: 1 = 1) (h2: 2 = 2): Exists (n => n = n) := MkEx 1 h1
def t4R (h1: 1 = 1) (h2: 2 = 2): Exists (n => n = n) := MkEx 2 h2
def t4pL (h1: 1 = 1) (h2: 1 = 1): Exists (n => n = n) := MkEx 1 h1
def t4pR (h1: 1 = 1) (h2: 1 = 1): Exists (n => n = n) := MkEx 1 h2
-- Test 8: skipping a proof field doesn't skip its neighbours.
type Checked: Type =
  | MkChecked (n: Nat) (ok: n = n)
def t8L (x: Nat) (y: Nat) (p: x = x) (q: y = y): Checked := MkChecked x p
def t8R (x: Nat) (y: Nat) (p: x = x) (q: y = y): Checked := MkChecked y q

-- For the memo tests: `wrap` glues, and unfolds to its argument.
def wrap [a: Prop] (b: Box a): Box a := b
def zero [a: Prop] (b: Box a): Nat := 0
type P2 (a: Prop): Type =
  | MkP2 (n: Nat) (b: Box a)
def memoL (a: Prop) (p: a) (q: a): P2 a :=
  let x := wrap (MkBox p)
  MkP2 (zero x) x
def memoR (a: Prop) (p: a) (q: a): P2 a :=
  let y := wrap (MkBox q)
  MkP2 (zero y) y

-- For the tree memo test: `pickA` and `pickB` are different definitions
-- stuck on `n`, so they're compared by their case trees, whose leaves
-- differ only in a proof field. Inside `treeL`/`treeR`'s own tree
-- comparison (which keeps the memo open), field `b` compares them in the
-- normal mode (equal), and field `c` again inside the hidden `ob`'s
-- shortcut (different).
opaque def ob [a: Prop] (b: Box a): Box a := b
def pickA (a: Prop) (n: Nat) (p: a) (q: a): Box a := match n with
  | Zero => MkBox p
  | Succ _ => MkBox p
def pickB (a: Prop) (n: Nat) (p: a) (q: a): Box a := match n with
  | Zero => MkBox q
  | Succ _ => MkBox q
type Q2 (a: Prop): Type =
  | MkQ2 (b: Box a) (c: Box a)
def treeLgo (a: Prop) (m: Nat) (n: Nat) (p: a) (q: a): Q2 a := match m with
  | Zero => MkQ2 (pickA a n p q) (ob (pickA a n p q))
  | Succ _ => MkQ2 (pickA a n p q) (ob (pickA a n p q))
def treeRgo (a: Prop) (m: Nat) (n: Nat) (p: a) (q: a): Q2 a := match m with
  | Zero => MkQ2 (pickB a n p q) (ob (pickB a n p q))
  | Succ _ => MkQ2 (pickB a n p q) (ob (pickB a n p q))
def treeL (a: Prop) (m: Nat) (n: Nat) (p: a) (q: a): Q2 a := treeLgo a m n p q
def treeR (a: Prop) (m: Nat) (n: Nat) (p: a) (q: a): Q2 a := treeRgo a m n p q
"#;

/// The program, with test 29's chains `wrap (wrap (… (MkBox p)))` of the
/// depths given.
fn program() -> String {
    let mut text = PROGRAM.to_string();
    for depth in CHAINS {
        for (side, proof) in [("L", "p"), ("R", "q")] {
            let open = "wrap (".repeat(*depth);
            let close = ")".repeat(*depth);
            text.push_str(&format!(
                "def chain{depth}{side} (a: Prop) (p: a) (q: a): Box a := {open}MkBox {proof}{close}\n"
            ));
        }
    }
    text
}

const CHAINS: &[usize] = &[1, 2, 24];

fn find(g: &Ev, name: &str) -> DefId {
    DefId(
        g.env
            .defs()
            .iter()
            .position(|d| &**d.name() == name)
            .unwrap_or_else(|| panic!("no `{name}`")),
    )
}

/// The body of `name`, evaluated with fresh variables for its parameters
/// by the machine (`reference: false`) or the reference evaluator, as the
/// checker evaluates the two sides of an equation: so with gluing on, a
/// call in it is left glued, not forced.
fn applied(g: &Ev, name: &str, reference: bool) -> (usize, Value) {
    let id = find(g, name);
    let def = g.def(id);
    let arity = def.arity();
    let body = def.body().expect("a body").peel_lams(arity);
    let env: Vec<Value> = (0..arity).map(Value::var).collect();
    let value = if reference {
        reference::eval(g, &env, body).unwrap()
    } else {
        eval(g, &env, body).unwrap()
    };
    (arity, value)
}

/// The answers for case `name`: glued, glued with the shortcuts disabled,
/// unglued, and the reference evaluator's.
fn answers(g: &Ev, name: &str) -> [bool; 4] {
    let machine = |glue: bool, shortcuts: bool| {
        let was = g.machine.glue.replace(glue);
        set_shortcuts_disabled(!shortcuts);
        let (level, a) = applied(g, &format!("{name}L"), false);
        let (_, b) = applied(g, &format!("{name}R"), false);
        let same = conv(g, level, &a, &b).unwrap();
        set_shortcuts_disabled(false);
        g.machine.glue.set(was);
        same
    };
    let (level, a) = applied(g, &format!("{name}L"), true);
    let (_, b) = applied(g, &format!("{name}R"), true);
    [
        machine(true, true),
        machine(true, false),
        machine(false, true),
        reference::conv(g, level, &a, &b).unwrap(),
    ]
}

fn session() -> Session {
    let mut session = Session::eager();
    if let Err(e) = session.load("masks.sw", &program()) {
        panic!("{e:?}");
    }
    session
}

const CASES: &[(&str, bool)] = &[
    ("t1", false),
    ("t4", false),
    ("t4p", true),
    ("t8", false),
    ("t2", false),
    ("sameMod", true),
    ("t20", false),
    ("t20d", true),
    ("t20n", true),
    ("handBuilt", true),
    ("t3", true),
    ("t9", false),
    ("box", true),
    ("t19", false),
    ("t17", false),
    ("t17p", true),
    ("t18", false),
    ("t21", false),
    ("t21p", true),
    ("t27a", true),
    ("t27b", true),
    ("t23", false),
    ("t23p", true),
    ("t24", false),
    ("t25", false),
    ("t15", false),
    ("t15p", true),
    ("t22", false),
    ("t22p", true),
    ("t22f", true),
    // The same pair of glued calls, `wrap (MkBox p)` and `wrap (MkBox q)`,
    // first inside a shortcut (different: the field is compared) and then
    // in the normal mode (equal): `CallMemo` must keep the two apart.
    ("memo", true),
    ("chain24", true),
    // The same pair of stuck calls, found equal by their trees in the
    // normal mode, then met inside a shortcut, where they differ:
    // `TreeMemo` must keep the two apart.
    ("tree", false),
];

#[test]
fn every_case_gets_its_answer_four_ways() {
    let session = session();
    let g = &session.elab.ev();
    let mut wrong = Vec::new();
    for (name, expected) in CASES {
        let got = answers(g, name);
        if got.iter().any(|a| a != expected) {
            wrong.push(format!(
                "{name}: expected {expected}, got {got:?} (glued, no shortcuts, unglued, reference)"
            ));
        }
    }
    assert!(wrong.is_empty(), "{}", wrong.join("\n"));
}

/// Test 25's other half: where `ou` is transparent, its calls unfold, to
/// `p` and `q`.
#[test]
fn a_transparent_call_unfolds_to_different_proofs() {
    let session = session();
    let g = &session.elab.ev();
    let ou = find(g, "ou");
    let _set = g.machine.transparent.set(Rc::from([ou]));
    assert_eq!(answers(g, "t25"), [false; 4]);
}

/// The marks the cases rely on.
#[test]
fn the_marks() {
    let session = session();
    let g = &session.elab.ev();
    let marks = |name: &str| g.def(find(g, name)).inert_params().to_vec();
    assert_eq!(marks("cast"), [false; 4]);
    assert_eq!(marks("tokNat"), [false, false]);
    assert_eq!(marks("keep"), [false, false]);
    assert_eq!(marks("g"), [false]);
    assert_eq!(marks("fnEq"), [false, true]);
    assert_eq!(marks("grpA"), [false, false]);
    assert_eq!(marks("grpB"), [false, false]);
    assert_eq!(marks("quietA"), [false, true]);
    assert_eq!(marks("quietB"), [false, true]);
    assert_eq!(marks("myAbsurd"), [true]);
}

/// Test 29: two chains of glued calls differing only in the innermost proof
/// field take steps linear in their depth. Each inner pair is compared at
/// most once per mode.
#[test]
fn a_deep_chain_is_compared_in_linear_steps() {
    let session = session();
    let g = &session.elab.ev();
    let steps = |depth: usize| {
        let was = g.machine.glue.replace(true);
        let (level, a) = applied(g, &format!("chain{depth}L"), false);
        let (_, b) = applied(g, &format!("chain{depth}R"), false);
        let before = g.machine.budget.total_work();
        assert!(conv(g, level, &a, &b).unwrap(), "depth {depth}");
        let used = g.machine.budget.total_work() - before;
        g.machine.glue.set(was);
        used
    };
    let (one, two, deep) = (steps(1), steps(2), steps(24));
    let per_level = two - one;
    assert!(
        deep <= one + 23 * per_level * 2,
        "depth 1: {one} steps, 2: {two}, 24: {deep}"
    );
}
