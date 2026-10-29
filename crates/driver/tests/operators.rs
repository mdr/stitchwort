//! Operators through dictionaries (docs/proposals/interfaces.md §5.13,
//! §5.16, stage 5): what the examples can't show. The elaborated terms of
//! `+`, `if x < y` and `auto` proofs of `x < y` on `Nat` and `Int` are
//! today's (golden terms); building them directly (the bootstrap phase's
//! primitive lowering, D187) gives the same terms as finding and projecting
//! the dictionary; and §5.16's four cases.

use stitchwort_core::globals::Globals;
use stitchwort_core::{Icit, Term};
use stitchwort_driver::driver::Session;

/// Loads `source` (with `+ * < <=` on `Nat` and `Int` always going through
/// their dictionaries if `uniform`): the session.
fn load(source: &str, uniform: bool) -> Session {
    let mut session = Session::new();
    session.elab.uniform_operators = uniform;
    if let Err(errors) = session.load("test.sw", source) {
        panic!("{errors:#?}");
    }
    session
}

/// The body of the definition called `name`, printed raw: every
/// application and argument, with definitions by name and variables by
/// index, so that two terms print the same only if they're the same.
fn body(session: &Session, name: &str) -> String {
    let g = &session.elab.globals;
    let def = g
        .defs
        .iter()
        .find(|d| &*d.name == name)
        .unwrap_or_else(|| panic!("no `{name}`"));
    raw(g, def.body().expect("a body"))
}

fn raw(g: &Globals, t: &Term) -> String {
    match t {
        Term::Loc(_, t) => raw(g, t),
        Term::Var(i) => format!("#{i}"),
        Term::Def(id) => g.def(*id).path.to_string(),
        Term::Nat(k) => k.to_string(),
        Term::Lam(_, icit, body) => format!("(fun {}{})", mark(*icit), raw(g, body)),
        Term::App(f, a, icit) => format!("({} {}{})", raw(g, f), mark(*icit), raw(g, a)),
        Term::Ctor(d, c, args) => {
            let name = &g.data(*d).ctors[*c].name;
            let args: Vec<String> = args.iter().map(|a| raw(g, a)).collect();
            format!("({name} {})", args.join(" "))
        }
        Term::Data(d, args) => {
            let args: Vec<String> = args.iter().map(|a| raw(g, a)).collect();
            format!("({} {})", g.data(*d).path, args.join(" "))
        }
        Term::Ann(t, ty) => format!("({} : {})", raw(g, t), raw(g, ty)),
        Term::Pi(_, icit, a, b) => format!("({}{} -> {})", mark(*icit), raw(g, a), raw(g, b)),
        Term::Eq(_, a, b) => format!("({} = {})", raw(g, a), raw(g, b)),
        Term::Let(_, _, v, b, _) => format!("(let {} in {})", raw(g, v), raw(g, b)),
        other => format!("{other:?}"),
    }
}

fn mark(icit: Icit) -> &'static str {
    match icit {
        Icit::Explicit => "",
        Icit::Implicit => "implicit ",
        Icit::Auto => "auto ",
    }
}

const SAMPLE: &str = "\
import Std (Nat)
def addNat (x: Nat) (y: Nat): Nat := x + y * 2
def addInt (x: Int) (y: Int): Int := x + y * 2
def leastNat (x: Nat) (y: Nat): Nat := if x < y then x else y
def leastInt (x: Int) (y: Int): Int := if x <= y then x else y
def leNat (x: Nat) (y: Nat): Bool := x <= y
def provedNat (x: Nat) (y: Nat) [auto ok: x < y]: Nat := y - x
def useNat: Nat := provedNat 1 2
def provedInt (x: Int) (y: Int) [auto ok: x < y]: Int := y - x
def useInt: Int := provedInt 1 2
theorem lawNat (x: Nat) (y: Nat): x + y = y + x := Nat.addComm x y
def withOrd [auto ord: Ord Nat] (x: Nat) (y: Nat): Nat := if x < y then x + y else x * y
def fromHypothesis (x: Nat) (y: Nat) (h: x < y): Nat := provedNat x y
def fromIf (x: Int) (y: Int): Int := if h: x < y then provedInt x y else 0
def before [auto ord: Ord a] (x: a) (y: a): Bool := if x < y then True else False
def beforeNat [auto ord: Ord Nat] (x: Nat) (y: Nat): Bool := if x < y then True else False
def Below [auto ord: Ord a] (x: a) (y: a): Prop := x < y
def below [auto ord: Ord a] (x: a) (y: a): Bool := if Below x y then True else False
def least (x: Nat) (y: Nat): Nat := if x < y then x else y
def textBefore (x: Text) (y: Text): Bool := if x < y then True else False
";

const NAMES: [&str; 19] = [
    "addNat",
    "addInt",
    "leastNat",
    "leastInt",
    "leNat",
    "provedNat",
    "useNat",
    "provedInt",
    "useInt",
    "lawNat",
    "withOrd",
    "fromHypothesis",
    "fromIf",
    "before",
    "beforeNat",
    "Below",
    "below",
    "least",
    "textBefore",
];

/// The terms on `Nat` and `Int`, as they were before stage 5 (checked
/// against the compiler of that time): `+` and `*` are the built-in
/// operations, and an `auto` proof of `x < y` is what it was (`Refl` for
/// numbers, the hypothesis or the `if`'s proof otherwise). `if x < y` whose
/// branches don't use the proof is the `Bool` `if` on the comparison's
/// `Bool` (`Nat.leq (Succ x) y`), since 28 Oct (9afc8973); `fromIf`, whose
/// branch uses it, is still decided by `Int.decLessThan`.
#[test]
fn golden_terms_on_nat_and_int() {
    let session = load(SAMPLE, false);
    let golden = [
        (
            "addNat",
            "(fun (fun ((Std.Nat.add #1) ((Std.Nat.mul #0) 2))))",
        ),
        (
            "addInt",
            "(fun (fun ((Std.Int.add #1) ((Std.Int.mul #0) (OfNat 2)))))",
        ),
        (
            "leastNat",
            "(fun (fun ((((Std.Bool.ifThenElse implicit (Std.Nat )) ((Std.Nat.leq (Succ #1)) \
             #0)) (fun #2)) (fun #1))))",
        ),
        (
            "leastInt",
            "(fun (fun ((((Std.Bool.ifThenElse implicit (Std.Int )) ((Std.Int.leq #1) #0)) (fun \
             #2)) (fun #1))))",
        ),
        ("leNat", "(fun (fun ((Std.Nat.leq #1) #0)))"),
        ("useNat", "(((Main.provedNat 1) 2) auto Refl)"),
        (
            "useInt",
            "(((Main.provedInt (OfNat 1)) (OfNat 2)) auto Refl)",
        ),
        ("lawNat", "(fun (fun ((Std.Nat.addComm #1) #0)))"),
        (
            "fromHypothesis",
            "(fun (fun (fun (((Main.provedNat #2) #1) auto #0))))",
        ),
        (
            "fromIf",
            "(fun (fun (((((Std.Decidable.elim implicit ((Std.Int.LessThan #1) #0)) implicit \
             (Std.Int )) ((Std.Int.decLessThan #1) #0)) (fun (((Main.provedInt #2) #1) auto \
             #0))) (fun (OfNat 0)))))",
        ),
    ];
    for (name, expected) in golden {
        assert_eq!(body(&session, name), expected, "{name}");
    }
}

/// D187: building `+ * < <=` on `Nat` and `Int` directly (as the bootstrap
/// phase does, and as later code does when no dictionary of the interface is
/// in scope) gives the same terms as finding the dictionary and projecting
/// its field.
#[test]
fn primitive_and_uniform_lowering_agree() {
    let primitive = load(SAMPLE, false);
    let uniform = load(SAMPLE, true);
    for name in NAMES {
        assert_eq!(body(&primitive, name), body(&uniform, name), "{name}");
    }
}

/// The same on a larger sample: the library files the AoC project uses,
/// and the project, loaded both ways, give every definition the same hash.
#[test]
fn primitive_and_uniform_lowering_agree_on_the_library_and_aoc() {
    use stitchwort_core::hash::def_hash;
    use stitchwort_driver::project::{DiskFiles, Target};
    let hashes = |uniform: bool| {
        let mut session = Session::new();
        session.elab.uniform_operators = uniform;
        let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../aoc");
        if let Err(errors) = session.load_project(&DiskFiles { root }, "aoc", &Target::Everything) {
            panic!("aoc doesn't load: {errors:#?}");
        }
        let g = &session.elab.globals;
        let mut out = std::collections::BTreeMap::new();
        for (i, def) in g.defs.iter().enumerate() {
            let h = def_hash(g, stitchwort_core::DefId(i))
                .unwrap()
                .map(|h| h.hex());
            out.insert(def.path.to_string(), h);
        }
        out
    };
    let (primitive, uniform) = (hashes(false), hashes(true));
    assert!(primitive.len() > 1000, "{} definitions", primitive.len());
    assert_eq!(primitive.len(), uniform.len());
    for (name, h) in &primitive {
        assert_eq!(Some(h), uniform.get(name), "{name}");
    }
}

/// §5.16's acceptance cases, by the terms: a generic `if x < y` is decided
/// by `Ord.decLessThan` from the same dictionary, `ord` (step 2), its
/// `Bool` taken by `Decidable.toBool` since neither branch uses the proof; a
/// predicate behind a definition is unfolded and decided the same way (step
/// 5, then 2); `beforeNat`, given `Nat.descending` by name, decides with its
/// dictionary's decider, not `Nat.decLessThan` (so it agrees with `before`:
/// `examples/accept/operators.sw` runs both); and a concrete `Nat`
/// conditional is today's term (`golden_terms_on_nat_and_int`'s
/// `leastNat`).
#[test]
fn relation_deciders_come_from_the_same_dictionary() {
    let session = load(SAMPLE, false);
    let decided = |name: &str| body(&session, name);
    assert_eq!(
        decided("before"),
        "(fun implicit (fun auto (fun (fun ((((Std.Bool.ifThenElse implicit (Std.Bool )) \
         ((Std.Decidable.toBool implicit ((((Std.Ord.lessThan implicit #3) auto #2) #1) #0)) \
         ((((Std.Ord.decLessThan implicit #3) auto #2) #1) #0))) (fun (True ))) (fun (False \
         )))))))"
    );
    assert_eq!(
        decided("below"),
        "(fun implicit (fun auto (fun (fun ((((Std.Bool.ifThenElse implicit (Std.Bool )) \
         ((Std.Decidable.toBool implicit ((((Main.Below implicit #3) auto #2) #1) #0)) \
         ((((Std.Ord.decLessThan implicit #3) auto #2) #1) #0))) (fun (True ))) (fun (False \
         )))))))"
    );
    assert_eq!(
        decided("beforeNat"),
        "(fun auto (fun (fun ((((Std.Bool.ifThenElse implicit (Std.Bool )) \
         ((Std.Decidable.toBool implicit ((((Std.Ord.lessThan implicit (Std.Nat )) auto #2) \
         #1) #0)) ((((Std.Ord.decLessThan implicit (Std.Nat )) auto #2) #1) #0))) (fun (True \
         ))) (fun (False ))))))"
    );
    assert_eq!(decided("least"), decided("leastNat"));
    // A global instance whose relation is a lambda isn't projected; its
    // decider comes from the same dictionary, by name, as written.
    assert_eq!(
        decided("textBefore"),
        "(fun (fun ((((Std.Bool.ifThenElse implicit (Std.Bool )) ((Std.Decidable.toBool \
         implicit ((((Std.Ord.lessThan implicit (Std.Text )) auto Std.Text.instOrd) #1) #0)) \
         ((((Std.Ord.decLessThan implicit (Std.Text )) auto Std.Text.instOrd) #1) #0))) (fun \
         (True ))) (fun (False )))))"
    );
    // With a dictionary of `Ord Nat` in scope, `<` uses it; `+` and `*`
    // still find the library's `Add` and `Mul`, projected.
    assert_eq!(
        decided("withOrd"),
        "(fun auto (fun (fun ((((Std.Bool.ifThenElse implicit (Std.Nat )) \
         ((Std.Decidable.toBool implicit ((((Std.Ord.lessThan implicit (Std.Nat )) auto #2) \
         #1) #0)) ((((Std.Ord.decLessThan implicit (Std.Nat )) auto #2) #1) #0))) (fun \
         ((Std.Nat.add #2) #1))) (fun ((Std.Nat.mul #2) #1))))))"
    );
}

/// A user's instance is projected like the library's: `p + q` on `Point`
/// is `Point.add p q`, and generic code keeps the method.
#[test]
fn a_users_instance_is_projected() {
    let source = "\
import Std (Int)
type Point = { x: Int, y: Int }
def Point.add (p: Point) (q: Point): Point := { x = p.x + q.x, y = p.y + q.y }
theorem Point.zeroAdd: (p: Point) -> Point.add { x = 0, y = 0 } p = p
  | { x, y } => rewrite Int.zeroAdd x, Int.zeroAdd y in rfl
theorem Point.assoc (p: Point) (q: Point) (r: Point): Point.add (Point.add p q) r = Point.add p (Point.add q r) :=
  rewrite Int.addAssoc p.x q.x r.x, Int.addAssoc p.y q.y r.y in rfl
theorem Point.comm (p: Point) (q: Point): Point.add p q = Point.add q p :=
  rewrite Int.addComm p.x q.x, Int.addComm p.y q.y in rfl
instance Point.instAdd: Add Point :=
  { zero = { x = 0, y = 0 }, add = Point.add, zeroAdd = Point.zeroAdd, assoc = Point.assoc, comm = Point.comm }
def plus (p: Point) (q: Point): Point := p + q
def twice [auto add: Add a] (x: a): a := x + x
";
    let session = load(source, false);
    assert_eq!(
        body(&session, "plus"),
        "(fun (fun ((Main.Point.add #1) #0)))"
    );
    assert_eq!(
        body(&session, "twice"),
        "(fun implicit (fun auto (fun ((((Std.Add.add implicit #2) auto #1) #0) #0))))"
    );
}

/// The direct lowering on `Nat` and `Int` (stage 5, item 3) is skipped
/// whenever a dictionary of the operator's interface is in scope, even one
/// whose type isn't settled yet (`d: Add ?t`, fixed only by a later use) or
/// whose own value still has a dictionary to find (`pick`'s): then `+`
/// resolves by §5.5, which waits for `?t` and chooses `d`, as uniform
/// lowering does. It never falls back to `Nat.add` while a local
/// dictionary could match.
#[test]
fn a_local_dictionary_not_yet_settled_is_used() {
    let source = "\
import Std (Nat)
def other: Add Nat := Nat.instAdd
def pick [auto add: Add a]: Add a := add

def later (x: Nat): Nat :=
  let k := (d: Add _) => x + x
  k other

def pending (x: Nat): Nat :=
  let d: Add Nat := pick
  x + x
";
    let (direct, uniform) = (load(source, false), load(source, true));
    for name in ["later", "pending"] {
        let term = body(&direct, name);
        assert_eq!(term, body(&uniform, name), "{name}");
        assert!(
            term.contains("Std.Add.add implicit (Std.Nat )) auto #"),
            "{name}: {term}"
        );
        assert!(!term.contains("Std.Nat.add"), "{name}: {term}");
    }
    // In `later`, `?t` is fixed only by `k other`: without it, `+` can't
    // tell whether `d` is the dictionary to use.
    let mut session = Session::new();
    let errors = session
        .load(
            "test.sw",
            "def never (x: Nat): Nat :=\n  let k := (d: Add _) => x + x\n  0\n",
        )
        .expect_err("`?t` is never fixed");
    let codes: Vec<&str> = errors.iter().map(|e| e.code).collect();
    assert_eq!(codes, ["E-INSTANCE-STUCK"]);
}
