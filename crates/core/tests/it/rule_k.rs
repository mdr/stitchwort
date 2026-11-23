//! Rule K (docs/core.md, "The equality rule"): a cast into data whose ends
//! are equal is its base. The ends are compared while evaluating, where no
//! context counts the variables in scope, so the comparison's fresh
//! variables come from a range no context reaches
//! (docs/proposals/full-proof-irrelevance-audit.md, finding A).

use crate::common::*;
use stitchwort_core::Value;
use stitchwort_core::value::{Ends, conv, ends_meet, eval};

/// With six variables in scope, `z => z` and `z => v5` differ. Compared at
/// level 5, the fresh variable for `z` would be `v5` itself and the two
/// would look equal; rule K's test must not be fooled.
#[test]
fn the_ends_test_makes_its_own_fresh_variables() {
    let p = Prelude::new();
    let g = p.g.ev();
    let env: Vec<Value> = (0..6).map(Value::var).collect();
    let nat = eval(&g, &[], &p.nat_ty()).unwrap();
    let identity = eval(&g, &env, &lam("z", v(0))).unwrap();
    let constant = eval(&g, &env, &lam("z", v(1))).unwrap();
    assert!(
        conv(&g, 5, &identity, &constant).unwrap(),
        "at too low a level, the fresh variable is `v5`"
    );
    let ends = Ends {
        ty: nat.clone(),
        x: identity.clone(),
        y: constant,
    };
    assert!(!ends_meet(&g, &ends).unwrap());
    let same = Ends {
        ty: nat.clone(),
        x: identity.clone(),
        y: identity,
    };
    assert!(ends_meet(&g, &same).unwrap());
}
