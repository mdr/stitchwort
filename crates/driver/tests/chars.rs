//! `Char` is an ordinary data type whose constructor carries a proof that its
//! code is a Unicode scalar value. These tests hand the kernel `MkChar` terms
//! directly, without the elaborator, to show that it's the kernel that refuses
//! a code that isn't one.

use stitchwort_core::check::infer_closed;
use stitchwort_core::{BigUint, DataId, Globals, Term};
use stitchwort_driver::driver::Session;
use stitchwort_syntax::{SourceMap, Span};

fn mk_char(g: &Globals) -> DataId {
    DataId(
        g.datas
            .iter()
            .position(|d| &*d.name == "Char")
            .expect("the prelude defines `Char`"),
    )
}

fn span() -> Span {
    Span::point(SourceMap::new().add("kernel", ""), 0)
}

/// `MkChar code rfl`, checked by the kernel. For a code that isn't a scalar
/// value, `rfl` would have to prove `False = True`.
fn check_code(g: &Globals, code: u32) -> Result<(), &'static str> {
    let term = Term::ctor(
        mk_char(g),
        0,
        vec![Term::Nat(BigUint::from(code).into()), Term::Refl],
    );
    infer_closed(g, &term, span())
        .map(|_| ())
        .map_err(|d| d.code)
}

#[test]
fn the_kernel_accepts_exactly_the_scalar_values() {
    let session = Session::new();
    let g = &session.elab.globals;
    for code in [
        0, 0x41, 0xD7FF, 0xE000, 0xFFFF, 0x1_0000, 0x1F600, 0x10_FFFF,
    ] {
        assert_eq!(check_code(g, code), Ok(()), "U+{code:X}");
    }
    for code in [
        0xD800,
        0xDBFF,
        0xDC00,
        0xDFFF,
        0x11_0000,
        0x11_0001,
        0xFFFF_FFFF,
    ] {
        assert_eq!(check_code(g, code), Err("E-REFL"), "U+{code:X}");
    }
}

#[test]
fn the_kernel_refuses_a_char_without_its_proof() {
    let session = Session::new();
    let g = &session.elab.globals;
    let term = Term::ctor(mk_char(g), 0, vec![Term::Nat(BigUint::from(65u32).into())]);
    assert_eq!(
        infer_closed(g, &term, span())
            .map(|_| ())
            .map_err(|d| d.code),
        Err("E-MALFORMED")
    );
}
