//! The kernel's comparison with two proofs equal (rule I, docs/core.md
//! "Proof irrelevance"), with rules K and S, and the pairs that must still
//! differ: data inside data, a cast whose ends differ. The cases began as
//! docs/proposals/proof-irrelevance.md §7's position masks; their comments
//! say which rule now answers. Each case is a pair
//! of definitions with the same parameters, `<case>L` and `<case>R`, whose
//! bodies are compared applied to fresh variables, by `value::conv` with
//! gluing on, with the shortcuts disabled and with gluing off, and by
//! `reference::conv`: all four must give the expected answer. These are the
//! kernel's half of §8's tests (the elaborator's unifier gets the same rules
//! separately).

use std::rc::Rc;

use stitchwort_core::value::{Value, conv, eval, set_shortcuts_disabled};
use stitchwort_core::{DefId, Ev, Term, reference};
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

type Q39: Nat → Prop =
  | MkQ39 (w: 0 = 0): Q39 0

def q39Nat (x: Nat): Q39 x → Nat
  | MkQ39 w => 5

type AtThree (a: Nat): Nat → Prop =
  | MkAtThree (h: a = 3) (k: 3 = a): AtThree a 0

def three (a: Nat): AtThree a 0 → Nat
  | MkAtThree h k => 5

def threeAt (a: Nat) (x: Nat): AtThree a x → Nat
  | MkAtThree h k => 5

type ByProof: (0 = 0) → Prop =
  | MkByProof (h: 0 = 0): ByProof h

def byProof (h: 0 = 0): ByProof h → Nat
  | MkByProof k => 5

-- A proof field bound by an enclosing match, its type `Q39 k` over the
-- enclosing type's parameter.
type Around39 (k: Nat): Prop =
  | MkAround39 (q: Q39 k)

def around39 (k: Nat): Around39 k → Nat
  | MkAround39 q => match q with
    | MkQ39 w => 5


type Mid39 (k: Nat): Prop =
  | MkMid39 (q: Q39 k)
type Top39 (k: Nat): Prop =
  | MkTop39 (m: Mid39 k)
def top39 (k: Nat): Top39 k → Nat
  | MkTop39 m => match m with
    | MkMid39 q => match q with
      | MkQ39 w => 9
type T39 (k: Nat): Type =
  | A39 (q: Q39 0)
  | B39 (q: Q39 k)
def ft39 (k: Nat): T39 k → Nat
  | A39 q => match q with
    | MkQ39 w => 5
  | B39 q => match q with
    | MkQ39 w => 6
type P239 (a: Nat) (b: Nat): Prop =
  | MkP239 (x: Q39 a) (y: Q39 b)
def fy39 (a: Nat) (b: Nat): P239 a b → Nat
  | MkP239 x y => match y with
    | MkQ39 w => 5
type BoxK (k: Nat) = { n: Nat, m: Nat, q: Q39 k }
def gbk (k: Nat): BoxK k → Nat
  | { n, m, q } => match q with
    | MkQ39 w => 4
type BoxM = { n: Nat, m: Nat, q: Q39 m }
def gbm: BoxM → Nat
  | { n, m, q } => match q with
    | MkQ39 w => 4
def h39: Nat → (k: Nat) → Around39 k → Nat
  | 0, k, o => 1
  | Succ m, k, MkAround39 q => match q with
    | MkQ39 w => 2
type Q339: Nat → Prop =
  | MkQ339 (w: 0 = 0): Q339 3
type W39: Nat → Prop =
  | MkW39 (q: Q339 3): W39 0
def fw39 (n: Nat): W39 n → Nat
  | MkW39 q => match q with
    | MkQ339 w => 5
type W239 (k: Nat): Nat → Prop =
  | MkW239 (q: Q39 k): W239 k k
def fw239 (k: Nat) (i: Nat): W239 k i → Nat
  | MkW239 q => match q with
    | MkQ39 w => 5

type TBox: Type 1 =
  | MkTBox (t: Type)

-- Recursive, so its stuck calls are compared by their arguments alone: a
-- definition that opens by tree would also be compared by its case tree,
-- where an argument it never computes with makes no difference (G6,
-- docs/core.md). `t` is only passed on, as an inert proof would be.
def choose (t: Type) (n: Nat): Nat :=
  match n with
    | Zero => 0
    | Succ m => choose t m

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
    | Zero => byComputing
    | Succ m => byComputing

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
-- Test 17: a cast whose ends agree (`a` and `a`) computes by rule K whatever its proof,
-- so the two sides are equal (SW-4673).
def t17L (a: Type) (h: a = a) (x: a): a := cast a a byComputing x
def t17R (a: Type) (h: a = a) (x: a): a := cast a a h x
def t17pL (a: Type) (h: a = a) (x: a): a := cast a a byComputing x
def t17pR (a: Type) (h: a = a) (x: a): a := x
-- Test 18: `tokNat` takes `t` apart; `Tok` has one shape and no fields, so the match
-- takes its branch by rule S whatever `t` is (SW-4673).
def t18L (t: Tok): Nat := tokNat t 0
def t18R (t: Tok): Nat := tokNat MkTok 0
-- Test 39: `Q39` is indexed and its constructor has a proof field; at the
-- constructor's index the match takes its branch by rule S whatever `s` is
-- (SW-4686). The partner is at index 1, which `MkQ39` can't build: stuck.
def t39L (s: Q39 0): Nat := q39Nat 0 s
def t39R (s: Q39 0): Nat := 5
def t39pL (s: Q39 1): Nat := q39Nat 1 s
def t39pR (s: Q39 1): Nat := 5
-- Test 40: fields that mention the parameter `a`; the partner is at an
-- index `MkAtThree` can't build.
def t40L (a: Nat) (s: AtThree a 0): Nat := three a s
def t40R (a: Nat) (s: AtThree a 0): Nat := 5
def t40pL (a: Nat) (s: AtThree a 1): Nat := threeAt a 1 s
def t40pR (a: Nat) (s: AtThree a 1): Nat := 5
-- Test 41: the constructor's index is its field, compared with the
-- scrutinee's index `h` as two proofs, by rule I.
def t41L (h: 0 = 0) (s: ByProof h): Nat := byProof h s
def t41R (h: 0 = 0) (s: ByProof h): Nat := 5
-- Test 42: as test 39, on a field an enclosing match bound (SW-4690).
def t42L (o: Around39 0): Nat := around39 0 o
def t42R (o: Around39 0): Nat := 5
def t42pL (o: Around39 1): Nat := around39 1 o
def t42pR (o: Around39 1): Nat := 5
def x1L (t: Top39 0): Nat := top39 0 t
def x1R (t: Top39 0): Nat := 9
def x1pL (t: Top39 1): Nat := top39 1 t
def x1pR (t: Top39 1): Nat := 9
def x2L (q: Q39 0): Nat := ft39 0 (B39 q)
def x2R (q: Q39 0): Nat := 6
def x2pL (q: Q39 1): Nat := ft39 1 (B39 q)
def x2pR (q: Q39 1): Nat := 6
def x2aL (k: Nat) (q: Q39 0): Nat := ft39 k (A39 q)
def x2aR (k: Nat) (q: Q39 0): Nat := 5
def x3L (p: P239 1 0): Nat := fy39 1 0 p
def x3R (p: P239 1 0): Nat := 5
def x3pL (p: P239 0 1): Nat := fy39 0 1 p
def x3pR (p: P239 0 1): Nat := 5
def x4L (b: BoxK 0): Nat := gbk 0 b
def x4R (b: BoxK 0): Nat := 4
def x4pL (b: BoxK 1): Nat := gbk 1 b
def x4pR (b: BoxK 1): Nat := 4
def x4mL (q: Q39 0): Nat := gbm { n = 1, m = 0, q = q }
def x4mR (q: Q39 0): Nat := 4
def x4mpL (q: Q39 1): Nat := gbm { n = 0, m = 1, q = q }
def x4mpR (q: Q39 1): Nat := 4
def x4mvL (b: BoxM): Nat := gbm b
def x4mvR (b: BoxM): Nat := 4
def x5L (o: Around39 0): Nat := h39 3 0 o
def x5R (o: Around39 0): Nat := 2
def x5pL (o: Around39 1): Nat := h39 3 1 o
def x5pR (o: Around39 1): Nat := 2
def x5nL (n: Nat) (o: Around39 0): Nat := h39 (Succ n) 0 o
def x5nR (n: Nat) (o: Around39 0): Nat := 2
def x6L (x: W39 0): Nat := fw39 0 x
def x6R (x: W39 0): Nat := 5
def x6pL (x: W39 1): Nat := fw39 1 x
def x6pR (x: W39 1): Nat := 5
def x7L (x: W239 0 0): Nat := fw239 0 0 x
def x7R (x: W239 0 0): Nat := 5
def x7aL (x: W239 1 1): Nat := fw239 1 1 x
def x7aR (x: W239 1 1): Nat := 5
def x7bL (x: W239 0 1): Nat := fw239 0 1 x
def x7bR (x: W239 0 1): Nat := 5
-- Test 21 and its partner: equal by rule S, as test 18.
def t21L (t: Tok) (u: Tok): Nat := tokNat t 0
def t21R (t: Tok) (u: Tok): Nat := tokNat u 0
def t21pL (p: 0 ≠ 0) (q: 0 ≠ 0): Nat := Void.absurd (p byComputing)
def t21pR (p: 0 ≠ 0) (q: 0 ≠ 0): Nat := Void.absurd (q byComputing)
-- Test 27: comparing by case trees doesn't compare impossible scrutinees.
def t27aL (p: 0 ≠ 0) (q: 0 ≠ 0): Nat := Void.absurd (q byComputing)
def t27aR (p: 0 ≠ 0) (q: 0 ≠ 0): Nat := myAbsurd (q byComputing)
def t27bL (p: 0 ≠ 0) (q: 0 ≠ 0): Nat := Void.absurd (p byComputing)
def t27bR (p: 0 ≠ 0) (q: 0 ≠ 0): Nat := myAbsurd (q byComputing)
-- Test 23: a parameter stored in a field isn't inert.
def t23L (d: Nat) (p: d ≠ 0) (q: d ≠ 0): d ≠ 0 := Box.unbox (keep d p)
def t23R (d: Nat) (p: d ≠ 0) (q: d ≠ 0): d ≠ 0 := Box.unbox (keep d q)
def t23pL (d: Nat) (p: d ≠ 0) (q: d ≠ 0): Box (d ≠ 0) := keep d p
def t23pR (d: Nat) (p: d ≠ 0) (q: d ≠ 0): Box (d ≠ 0) := keep d q
-- Test 24: masks stop at the arity.
def t24L (n: Nat) (h: 0 = 0): Bool := g n byComputing
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
    // Each parameter marked as its binder is, as the checker binds it.
    let mut marks = Vec::new();
    let mut ty = def.ty().strip_loc();
    while let Term::Pi(_, _, _, cod, mark) = ty {
        marks.push(*mark);
        ty = cod.strip_loc();
    }
    let env: Vec<Value> = (0..arity)
        .map(|l| Value::var_marked(l, marks.get(l).copied().unwrap_or_default()))
        .collect();
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
    // Rule I: both sides are proofs (of `Exists`), so the data field inside
    // isn't looked at.
    ("t4", true),
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
    // Rule I: the results are proofs of `a` (before it, the shortcut
    // compared the field).
    ("t19", true),
    // Rule K: the cast's ends are `a` and `a`, so it computes whatever `h`.
    ("t17", true),
    ("t17p", true),
    // Rule S: `Tok` has one constructor, so `tokNat` takes its branch
    // without looking at `t`.
    ("t18", true),
    // Rule S on an indexed proposition with a proof field, at agreeing
    // indices; at apart ones the match stays stuck.
    ("t39", true),
    ("t39p", false),
    // The same with fields that mention a parameter, and with an index
    // that is the constructor's field.
    ("t40", true),
    ("t40p", false),
    ("t41", true),
    // The same on a field an enclosing match bound.
    ("t42", true),
    ("t42p", false),
    ("x1", true),
    ("x1p", false),
    ("x2", true),
    ("x2p", false),
    ("x2a", true),
    ("x3", true),
    ("x3p", false),
    ("x4", true),
    ("x4p", false),
    ("x4m", true),
    ("x4mp", false),
    ("x4mv", false),
    ("x5", true),
    ("x5p", false),
    ("x5n", true),
    ("x6", true),
    ("x6p", false),
    ("x7", true),
    ("x7a", false),
    ("x7b", false),
    // Rule S, as test 18.
    ("t21", true),
    ("t21p", true),
    ("t27a", true),
    ("t27b", true),
    // Rule I: the results are proofs.
    ("t23", true),
    ("t23p", true),
    // Rule I: `h` and `byComputing` are proofs, compared as `g`'s
    // arguments however many `g` takes.
    ("t24", true),
    // Rule I: the results are proofs of `a`.
    ("t25", true),
    ("t15", false),
    ("t15p", true),
    // Rule I: `h1` and `h2` are proofs, whatever the group does with them.
    ("t22", true),
    ("t22p", true),
    ("t22f", true),
    // The same pair of glued calls, `wrap (MkBox p)` and `wrap (MkBox q)`,
    // first inside a shortcut (different: the field is compared) and then
    // in the normal mode (equal): `CallMemo` must keep the two apart.
    ("memo", true),
    ("chain24", true),
    // The same pair of stuck calls, compared by their trees and again
    // inside the hidden `ob`'s arguments: equal both times by rule I, where
    // the shortcut mode once made them differ the second time.
    ("tree", true),
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
/// `p` and `q`, two proofs of `a`: equal by rule I either way.
#[test]
fn a_transparent_call_unfolds_to_proofs_still_equal() {
    let session = session();
    let g = &session.elab.ev();
    let ou = find(g, "ou");
    let _set = g.machine.transparent.set(Rc::from([ou]));
    assert_eq!(answers(g, "t25"), [true; 4]);
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

/// The kernel derives every mark and trusts none it is given (the SW-4671
/// review's F5): each case's checked body, with its marks cleared, checks
/// again to the same marks.
#[test]
fn cleared_marks_are_derived_again() {
    let session = session();
    let g = &session.elab.ev();
    let span = g.def(find(g, "t1L")).span();
    let mut compared = 0;
    for (name, _) in CASES {
        for side in ["L", "R"] {
            let def = g.def(find(g, &format!("{name}{side}")));
            let Some(body) = def.body() else { continue };
            let annotated = |strip: bool| {
                let (body, ty) = if strip {
                    (
                        body.without_marks(g).unwrap(),
                        def.ty().without_marks(g).unwrap(),
                    )
                } else {
                    ((**body).clone(), def.ty().clone())
                };
                stitchwort_core::check::infer_closed(
                    g,
                    &Term::Ann(Rc::new(body), Rc::new(ty)),
                    span,
                )
            };
            // A body with a case tree is checked only as a definition's.
            let Ok((checked, _)) = annotated(false) else {
                continue;
            };
            let (again, _) = annotated(true).expect("checks with its marks cleared");
            assert_eq!(checked.marks(), again.marks(), "{name}{side}");
            assert!(
                !again.marks().contains(&stitchwort_core::ProofMark::Unknown),
                "{name}{side}"
            );
            compared += 1;
        }
    }
    assert!(compared >= 10, "only {compared} bodies compared");
}
