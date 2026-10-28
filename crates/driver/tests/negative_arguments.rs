//! A negative argument elaborates to the term its bracketed form does
//! (docs/proposals/negative-arguments.md §4.2, "Hashes"): `f -2` and
//! `f (-2)` have the same hash, and so do `-1.abs` and `(-1).abs`.

use stitchwort_core::DefId;
use stitchwort_core::hash::def_hash;
use stitchwort_driver::driver::Session;

const SOURCE: &str = "\
import Std (Float, Int, List)

def f (n: Int): Int := n + 10
def g (a: Int) (b: Int) (c: Int): Int := a + b + c

def argument: Int := f -2
def bracketed: Int := f (-2)

def named (x: Int): Int := f -x
def namedBracketed (x: Int): Int := f (-x)

def middle: Int := g 1 -2 3
def middleBracketed: Int := g 1 (-2) 3

def method: Int := f -3.neg
def methodBracketed: Int := f ((-3).neg)

def floored: Float := -2.5.floor
def flooredBracketed: Float := (-2.5).floor
";

#[test]
fn a_negative_argument_has_the_hash_of_its_bracketed_form() {
    let mut session = Session::eager();
    if let Err(errors) = session.load("negative.sw", SOURCE) {
        panic!("{errors:#?}");
    }
    let g = &session.elab.globals;
    let _op = g.budget.operation(stitchwort_core::Limits::default());
    let hash = |name: &str| {
        let id = (0..g.defs.len())
            .map(DefId)
            .find(|d| g.def(*d).path.ends_with(&format!(".{name}")) || &*g.def(*d).path == name)
            .unwrap_or_else(|| panic!("no `{name}`"));
        def_hash(g, id).unwrap().unwrap().hex()
    };
    for (written, bracketed) in [
        ("argument", "bracketed"),
        ("named", "namedBracketed"),
        ("middle", "middleBracketed"),
        ("method", "methodBracketed"),
        ("floored", "flooredBracketed"),
    ] {
        assert_eq!(
            hash(written),
            hash(bracketed),
            "`{written}` elaborates differently from `{bracketed}`"
        );
    }
}
