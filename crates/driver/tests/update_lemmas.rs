//! Update lemmas (docs/proposals/variant-fields.md §6.6): `T.f.update.g`,
//! reading shared field `g` after an update of shared field `f`, for the
//! data types an update applies to. Using them in proofs is
//! `examples/accept/shared-field-update-lemmas.sw`.

use stitchwort_core::pretty;
use stitchwort_driver::driver::Session;
use stitchwort_syntax::Diagnostic;

fn load(source: &str) -> Session {
    let mut session = Session::new();
    if let Err(errors) = session.load("test.sw", source) {
        panic!("{errors:#?}");
    }
    session
}

fn errors(source: &str) -> Vec<Diagnostic> {
    let mut session = Session::new();
    session.load("test.sw", source).err().unwrap_or_default()
}

/// The update lemmas of type `ty`, as `name : statement`, in the order
/// they're declared (helpers left out).
fn lemmas(session: &Session, ty: &str) -> Vec<String> {
    let g = &session.elab.globals;
    let prefix = format!("{ty}.");
    g.defs
        .iter()
        .filter(|d| {
            d.name.starts_with(&prefix) && d.name.contains(".update.") && !d.name.contains('%')
        })
        .map(|d| format!("{} : {}", d.name, pretty::term_for_message(g, &[], &d.ty)))
        .collect()
}

const SHAPE: &str =
    "type Shape =\n  | Dot (ref: Nat) (id: Text)\n  | Circle (id: Text) (ref: Nat) (text: Text)\n";

#[test]
fn each_shared_field_gets_one_per_shared_field() {
    let session = load(SHAPE);
    let found = lemmas(&session, "Shape");
    let names: Vec<&str> = found
        .iter()
        .map(|l| l.split(" : ").next().unwrap())
        .collect();
    assert_eq!(
        names,
        [
            "Shape.ref.update.ref",
            "Shape.ref.update.id",
            "Shape.id.update.ref",
            "Shape.id.update.id",
        ],
        "{found:#?}"
    );
    // The same field: the new value. Another: the old value's.
    assert!(
        found[0].ends_with(").ref = ref") && found[0].contains("(x: Shape) → (ref: Nat) →"),
        "{}",
        found[0]
    );
    assert!(found[1].ends_with(").id = x.id"), "{}", found[1]);
}

#[test]
fn they_prove_what_they_say_and_rewrite_finds_them() {
    load(&format!(
        "{SHAPE}\n\
         def renumber (s: Shape): Shape := {{ s | ref = s.ref + 1 }}\n\n\
         theorem keepsId (s: Shape): (renumber s).id = s.id :=\n  rewrite Shape.ref.update.id in rfl\n\n\
         theorem bumps (s: Shape): (renumber s).ref = s.ref + 1 :=\n  rewrite Shape.ref.update.ref in rfl\n\n\
         theorem nested (s: Shape) (t: Text): ({{ {{ s | ref = 0 }} | id = t }}).ref = 0 :=\n  \
           rewrite Shape.id.update.ref, Shape.ref.update.ref in rfl\n\n\
         theorem applied (s: Shape): ({{ s | id = \"a\" }}).id = \"a\" := Shape.id.update.id s \"a\"\n"
    ));
}

#[test]
fn an_update_of_several_independent_fields_is_not_matched() {
    let found = errors(&format!(
        "{SHAPE}\n\
         theorem both (s: Shape): ({{ s | ref = 0, id = \"a\" }}).ref = 0 :=\n  \
           rewrite Shape.ref.update.ref in rfl\n"
    ));
    assert!(
        found.iter().any(|d| d.code == "E-REWRITE-NOTHING"),
        "{found:#?}"
    );
}

#[test]
fn a_field_that_forces_others_updates_them_too() {
    let session = load(
        "import Std (Vec)\n\n\
         type Sized =\n  | A (n: Nat) (xs: Vec Nat n) (name: Text)\n  | B (name: Text) (n: Nat) (xs: Vec Nat n)\n",
    );
    let found = lemmas(&session, "Sized");
    let names: Vec<&str> = found
        .iter()
        .map(|l| l.split(" : ").next().unwrap())
        .collect();
    // `xs` is never read back: after an update its type isn't `Vec Nat n`.
    assert_eq!(
        names,
        [
            "Sized.n.update.n",
            "Sized.n.update.name",
            "Sized.xs.update.n",
            "Sized.xs.update.name",
            "Sized.name.update.n",
            "Sized.name.update.name",
        ],
        "{found:#?}"
    );
    assert!(
        found[0].contains("(n: Nat) → (xs: Vec Nat n) →"),
        "{}",
        found[0]
    );
}

#[test]
fn a_field_an_update_cant_give_has_none() {
    // Replacing `n` forces the implicit `h`, which an update can't give.
    let session = load(
        "type Checked =\n  | A (n: Nat) [h: n = 0] (label: Text)\n  | B (n: Nat) [h: n = 0] (label: Text)\n",
    );
    let found = lemmas(&session, "Checked");
    let names: Vec<&str> = found
        .iter()
        .map(|l| l.split(" : ").next().unwrap())
        .collect();
    assert_eq!(
        names,
        ["Checked.label.update.n", "Checked.label.update.label"],
        "{found:#?}"
    );
}

#[test]
fn parameters_are_implicit() {
    let session =
        load("type Tagged (a: Type) =\n  | Plain (tag: a)\n  | Counted (count: Nat) (tag: a)\n");
    let found = lemmas(&session, "Tagged");
    assert_eq!(found.len(), 1, "{found:#?}");
    assert!(
        found[0].starts_with("Tagged.tag.update.tag : [a: Type] → (x: Tagged a) → (tag: a) →"),
        "{}",
        found[0]
    );
}

#[test]
fn records_indexed_families_and_propositions_have_none() {
    let session = load(
        "type Point = { x: Nat, y: Nat }\n\n\
         type Fam: Nat -> Type =\n  | FA (k: Nat) (label: Text): Fam 0\n  | FB (k: Nat) (label: Text): Fam 1\n\n\
         type Both (p: Prop) (q: Prop): Prop =\n  | MkBoth (left: p) (right: q)\n\n\
         theorem moved (p: Point) (n: Nat): ({ p | x = n }).y = p.y := rfl\n",
    );
    for ty in ["Point", "Fam", "Both"] {
        assert_eq!(lemmas(&session, ty), Vec::<String>::new(), "{ty}");
    }
}

#[test]
fn a_field_or_function_called_update_doesnt_clash() {
    let session = load(
        "type Change =\n  | Add (update: Nat) (x: Text)\n  | Drop (x: Text) (update: Nat)\n\n\
         def Change.update' (c: Change): Change := { c | update = 0 }\n\n\
         theorem cleared (c: Change): (c.update').update = 0 := rewrite Change.update.update.update in rfl\n\n\
         theorem kept (c: Change): (c.update').x = c.x := rewrite Change.update.update.x in rfl\n",
    );
    assert_eq!(lemmas(&session, "Change").len(), 4);
}

#[test]
fn every_lemma_of_the_core_checks() {
    // A lemma that didn't check would be declared and failed: the core's
    // types with shared fields have exactly these.
    let session = load("");
    let found = lemmas(&session, "Pair");
    assert_eq!(found.len(), 4, "{found:#?}");
    assert!(
        session
            .elab
            .globals
            .defs
            .iter()
            .all(|d| !d.name.contains(".update.") || d.body().is_some()),
        "a generated update lemma has no body"
    );
}
