//! Rule K (docs/core.md, "The equality rule"): a cast into data whose ends
//! are equal is its base. The ends are compared while evaluating, where no
//! context counts the variables in scope, so the comparison's fresh
//! variables come from a range no context reaches
//! (docs/proposals/full-proof-irrelevance-audit.md, finding A).

use crate::common::*;
use stitchwort_core::Value;
use stitchwort_core::value::{Ends, RESERVED_LEVELS, conv, ends_meet, eval};

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

/// A test whose levels would pass the top of the reserved range answers
/// "not equal" without comparing. Here the tests around it have taken all
/// but one of the levels above the base, so its first level, unchecked,
/// would wrap round to 0, and with `v0` in scope `z => z` and `z => v0`
/// would look equal (on a 32-bit target, a test inside 128 others).
#[test]
fn the_ends_test_out_of_levels_says_different() {
    let p = Prelude::new();
    let g = p.g.ev();
    let nat = eval(&g, &[], &p.nat_ty()).unwrap();
    let env = [Value::var(0)];
    let identity = eval(&g, &env, &lam("z", v(0))).unwrap();
    let constant = eval(&g, &env, &lam("z", v(1))).unwrap();
    let wrapping = Ends {
        ty: nat.clone(),
        x: identity.clone(),
        y: constant,
    };
    let full = (usize::MAX - RESERVED_LEVELS) + 1;
    g.machine.cast_levels.set(full);
    assert!(!ends_meet(&g, &wrapping).unwrap());
    let same = Ends {
        ty: nat,
        x: identity.clone(),
        y: identity,
    };
    assert!(
        !ends_meet(&g, &same).unwrap(),
        "out of levels, even equal ends are stuck"
    );
    assert_eq!(g.machine.cast_levels.get(), full);
    g.machine.cast_levels.set(0);
    assert!(!ends_meet(&g, &wrapping).unwrap());
    assert!(ends_meet(&g, &same).unwrap());
}
