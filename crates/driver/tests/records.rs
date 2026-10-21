//! Declared records (docs/proposals/records.md, stage 1): what the kernel
//! sees of them (a record flag, which it hashes and checks against the
//! constructor count, and decision procedures for proof fields, which it
//! type-checks), and what the elaborator generates (projections, `==`).
//! The surface behaviour is in `examples/accept/records.sw`,
//! `examples/accept/records-effects.sw`, `examples/extract/records.sw` and
//! the `record-*` rejects.

use stitchwort_core::check::{
    CtorDecl, add_field_validator, declare_data_group_as, define_data_group,
};
use stitchwort_core::hash::data_hash;
use stitchwort_core::{DataId, Globals, Sort, Term};
use stitchwort_driver::driver::{Cache, Outcome, Session};
use stitchwort_syntax::{SourceMap, Span};

fn span() -> Span {
    Span::point(SourceMap::new().add("kernel", ""), 0)
}

fn load(source: &str) -> Session {
    let mut session = Session::new();
    if let Err(errors) = session.load("test.sw", source) {
        panic!("{errors:#?}");
    }
    session
}

fn data(g: &Globals, name: &str) -> DataId {
    g.find_data(name).unwrap_or_else(|| panic!("no `{name}`"))
}

/// Declares `name` with constructors `ctors`, each `(name, fields)` with
/// fields of type `Nat`, as a record or not.
fn declare(
    g: &mut Globals,
    name: &str,
    record: bool,
    ctors: &[(&str, &[&str])],
) -> Result<DataId, &'static str> {
    let nat = Term::Data(data(g, "Nat"), Vec::new());
    let ids = declare_data_group_as(
        g,
        Vec::new(),
        Sort::Type(0),
        vec![(name.into(), span(), record)],
    )
    .map_err(|d| d.code)?;
    let ctors = ctors
        .iter()
        .map(|(c, fields)| CtorDecl {
            name: (*c).into(),
            fields: fields
                .iter()
                .map(|f| ((*f).into(), nat.clone(), span()))
                .collect(),
            result: Vec::new(),
            implicit: Vec::new(),
        })
        .collect();
    define_data_group(g, vec![(ids[0], ctors)]).map_err(|d| d.code)?;
    Ok(ids[0])
}

#[test]
fn the_record_flag_is_hashed() {
    let mut a = Session::new();
    let mut b = Session::new();
    let ga = &mut a.elab.globals;
    let gb = &mut b.elab.globals;
    let r = declare(ga, "Point", true, &[("Point.mk", &["x", "y"])]).unwrap();
    let d = declare(gb, "Point", false, &[("Point.mk", &["x", "y"])]).unwrap();
    let _op = ga.budget.operation(stitchwort_core::Limits::default());
    let ha = data_hash(ga, r).unwrap();
    drop(_op);
    let _op = gb.budget.operation(stitchwort_core::Limits::default());
    let hb = data_hash(gb, d).unwrap();
    assert!(ha.is_some() && hb.is_some());
    assert_ne!(
        ha, hb,
        "a record and a data type with the same constructor differ"
    );
}

#[test]
fn a_record_has_exactly_one_constructor() {
    let mut s = Session::new();
    let g = &mut s.elab.globals;
    assert_eq!(
        declare(g, "Two", true, &[("A", &[]), ("B", &[])]),
        Err("E-MALFORMED")
    );
    assert_eq!(declare(g, "None", true, &[]), Err("E-MALFORMED"));
    assert!(declare(g, "One", true, &[("One.mk", &["n"])]).is_ok());
    // An ordinary data type may have any number.
    assert!(declare(g, "Two'", false, &[("A'", &[]), ("B'", &[])]).is_ok());
}

/// The kernel checks a proof field's decision procedure: it must decide that
/// field's proposition, about the earlier fields, and only a proof field of
/// a final type can have one, once.
#[test]
fn field_validators_are_checked() {
    let mut s = load(
        "import Std (Nat)\n\n\
         def IsZero' (n : Nat) : Prop := n = 0\n\n\
         type Small = { n : Nat, zero : IsZero' n }\n\n\
         def decZero (n : Nat) : Decidable (IsZero' n) := Nat.decEq n 0\n\n\
         def decOne (n : Nat) : Decidable (n = 1) := Nat.decEq n 1\n",
    );
    let g = &mut s.elab.globals;
    let small = data(g, "Small");
    let decidable = data(g, "Decidable");
    let def = |g: &Globals, name: &str| {
        Term::Def(stitchwort_core::DefId(
            g.defs.iter().position(|d| &*d.name == name).unwrap(),
        ))
    };
    // In the context of the earlier field `n`, variable 0.
    let wrong = Term::app(def(g, "decOne"), Term::Var(0));
    let right = Term::app(def(g, "decZero"), Term::Var(0));
    let code = |r: Result<(), stitchwort_syntax::Diagnostic>| r.err().map_or("ok", |d| d.code);
    assert_eq!(
        code(add_field_validator(g, small, 0, 0, decidable, &right)),
        "E-MALFORMED",
        "`n` isn't a proof"
    );
    assert_eq!(
        code(add_field_validator(g, small, 0, 2, decidable, &right)),
        "E-MALFORMED",
        "no such field"
    );
    assert_eq!(
        code(add_field_validator(g, small, 0, 1, decidable, &wrong)),
        "E-TYPE-MISMATCH"
    );
    assert_eq!(
        code(add_field_validator(g, small, 0, 1, decidable, &right)),
        "ok"
    );
    assert_eq!(
        code(add_field_validator(g, small, 0, 1, decidable, &right)),
        "E-MALFORMED",
        "only one"
    );
    assert_eq!(g.data(small).validators.len(), 1);
}

/// Each field has a projection, `R.field`, whose type mentions earlier
/// fields as projections, and `==` is derived when it can be.
#[test]
fn projections_and_equality_are_generated() {
    let s = load(
        "import Std (List)\n\n\
         type Person = { name : Text, age : Nat }\n\n\
         type Sized = { items : List Nat, size : Nat, ok : List.length items = size }\n\n\
         type Box (a : Type) = { value : a }\n",
    );
    let g = &s.elab.globals;
    let shown = |name: &str| {
        let def = g
            .defs
            .iter()
            .find(|d| &*d.name == name)
            .unwrap_or_else(|| panic!("no `{name}`"));
        stitchwort_core::pretty::term(g, &[], &def.ty)
    };
    assert_eq!(shown("Person.age"), "Person -> Nat");
    assert_eq!(
        shown("Sized.ok"),
        "(r: Sized) -> List.length r.items = r.size"
    );
    assert_eq!(shown("Box.value"), "[a: Type] -> Box a -> a");
    // A derived `DecEq` instance (docs/proposals/interfaces.md §5.11), also
    // for a proof field that's an equation, and with parameters.
    for record in ["Person", "Sized", "Box"] {
        let name = format!("{record}.%instDecEq");
        let def = g
            .defs
            .iter()
            .find(|d| *d.name == *name)
            .unwrap_or_else(|| panic!("no `{name}`"));
        assert!(def.instance, "{name} is an instance");
        let ty = shown(&name);
        assert!(
            ty.contains(&format!("DecEq {record}")) || ty.contains(&format!("DecEq ({record}")),
            "{ty}"
        );
    }
}

/// Changing a record's fields changes what's generated for it, and the
/// derived `==` really decides: unequal in exactly one field is unequal.
#[test]
fn derived_equality_compares_every_field() {
    let s = load(
        "type P = { a : Nat, b : Bool, c : Text }\n\n\
         def base : P := { a = 1, b = True, c = \"x\" }\n\n\
         test \"same\" := base == { c = \"x\", b = True, a = 1 }\n\
         test \"a\" := not (base == { a = 2, b = True, c = \"x\" })\n\
         test \"b\" := not (base == { a = 1, b = False, c = \"x\" })\n\
         test \"c\" := not (base == { a = 1, b = True, c = \"y\" })\n",
    );
    let results = s.run_tests(&Cache::disabled());
    assert_eq!(results.len(), 4);
    for r in results {
        assert!(matches!(r.outcome, Outcome::Passed), "{}", r.name);
    }
}
