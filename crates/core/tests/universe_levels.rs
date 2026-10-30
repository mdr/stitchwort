//! SW-902: the kernel refuses a universe with no universe above it, on
//! hand-built terms that skip the parser and the elaborator. Before the fix,
//! `Sort::succ` added one unchecked, so in release `Type u32::MAX : Type 0`
//! and the hierarchy was cyclic. These are the trust-boundary tests: the
//! parser's and the elaborator's limits are only conveniences.

mod common;

use common::*;
use stitchwort_core::check::{self, DataDecl, infer_closed};
use stitchwort_core::{MAX_LEVEL, Sort, Term};

fn infer_code(term: &Term) -> &'static str {
    let p = Prelude::new();
    infer_closed(&p.g, term, span())
        .err()
        .map_or("ok", |d| d.code)
}

#[test]
fn refuses_the_largest_u32_level() {
    assert_eq!(infer_code(&Term::Sort(Sort::Type(u32::MAX))), "E-UNIVERSE");
}

#[test]
fn refuses_the_top_universe_and_accepts_the_one_below() {
    assert_eq!(infer_code(&ty_n(MAX_LEVEL)), "E-UNIVERSE");
    assert_eq!(infer_code(&ty_n(MAX_LEVEL + 1)), "E-UNIVERSE");
    let p = Prelude::new();
    let (_, t) = infer_closed(&p.g, &ty_n(MAX_LEVEL - 1), span()).expect("checks");
    assert!(matches!(t, stitchwort_core::Value::Sort(Sort::Type(l)) if l == MAX_LEVEL));
}

#[test]
fn the_parser_and_the_kernel_agree_on_the_limit() {
    assert_eq!(MAX_LEVEL, stitchwort_syntax::MAX_UNIVERSE_LEVEL);
    assert_eq!(Sort::Type(MAX_LEVEL).succ(), None);
    assert_eq!(Sort::Type(u32::MAX).succ(), None);
    assert_eq!(Sort::Prop.succ(), Some(Sort::Type(0)));
}

/// `def wrap: Type 0 := Type 4294967295` and
/// `def wrap2: Type 4294967295 := Type 4294967294`.
#[test]
fn refuses_the_wrapping_definitions() {
    let mut p = Prelude::new();
    assert_eq!(
        define(&mut p.g, "wrap", ty_n(0), ty_n(u32::MAX)),
        Err("E-UNIVERSE")
    );
    assert_eq!(
        define(&mut p.g, "wrap2", ty_n(u32::MAX), ty_n(u32::MAX - 1)),
        Err("E-UNIVERSE")
    );
}

/// `(A : Type 4294967295) -> A` has no universe either: its domain is
/// refused before `Sort::pi` takes a maximum.
#[test]
fn refuses_a_pi_over_the_largest_level() {
    assert_eq!(infer_code(&pi("A", ty_n(u32::MAX), v(0))), "E-UNIVERSE");
}

/// `type Box: Type 0 = MkBox (t: Type 4294967295)`.
#[test]
fn refuses_a_field_of_the_largest_level() {
    let mut p = Prelude::new();
    let d = data(&mut p.g, "Box", vec![], Sort::Type(0));
    let code = check::define_ctors(
        &mut p.g,
        d,
        vec![ctor("MkBox", vec![("t", ty_n(u32::MAX))])],
    )
    .err()
    .map_or("ok", |e| e.code);
    assert_eq!(code, "E-UNIVERSE");
}

/// A data type declared in a universe with nothing above it, checked or
/// admitted as trusted (the check cache's path).
#[test]
fn refuses_a_data_type_in_a_universe_with_no_type() {
    let decl = || DataDecl {
        name: "Big".into(),
        span: span(),
        record: false,
        indices: Vec::new(),
    };
    for level in [MAX_LEVEL, u32::MAX] {
        let mut p = Prelude::new();
        let declared =
            check::declare_indexed_data_group(&mut p.g, vec![], Sort::Type(level), vec![decl()]);
        assert_eq!(declared.err().map(|d| d.code), Some("E-UNIVERSE"));
        let admitted =
            check::admit_trusted_data_decls(&mut p.g, vec![], Sort::Type(level), vec![decl()]);
        assert_eq!(admitted.err().map(|d| d.code), Some("E-UNIVERSE"));
    }
    let mut p = Prelude::new();
    let declared = check::declare_indexed_data_group(
        &mut p.g,
        vec![],
        Sort::Type(MAX_LEVEL - 1),
        vec![decl()],
    );
    assert!(declared.is_ok());
}
