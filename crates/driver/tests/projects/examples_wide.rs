//! Tests that run over every example and take minutes, kept out of the
//! module of the area they check (`check_cache::`, `rewind::`) so that a lane's filter
//! for that area doesn't sweep them in (SW-4704).

use stitchwort_driver::driver::par_map;

use crate::check_cache::{STACK, assert_cache_changes_nothing, examples};
use crate::rewind;

/// With navigation recorded, which covers more of what an entry holds; the
/// whole library without it is checked above.
#[test]
fn the_cache_changes_nothing_for_the_examples() {
    let sources = examples();
    par_map(STACK, &sources, |source| {
        assert_cache_changes_nothing(source, true);
    });
}

/// The caches are caches: the examples' sample checked with them emptied
/// before every declaration gives what a fresh check gives.
#[test]
fn emptying_the_caches_changes_nothing_for_the_examples() {
    let sources = rewind::examples();
    par_map(rewind::STACK, &sources, |source| {
        rewind::check_with_cleared_caches(source, &rewind::fresh(source));
    });
}

#[test]
fn rewinding_changes_nothing_for_the_examples() {
    let sources = rewind::examples();
    par_map(
        rewind::STACK,
        &sources,
        rewind::assert_rewinding_changes_nothing,
    );
}
