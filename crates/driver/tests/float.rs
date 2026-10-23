//! `Float` (docs/proposals/float.md): the kernel's definitional agreement
//! gate (§3.4, D731), the bindings pinned by content hash, and the
//! contract plumbing (§3.3).

use stitchwort_core::Limits;
use stitchwort_core::float;
use stitchwort_driver::driver::Session;
use stitchwort_driver::float_gate::{self, Mode};

/// Every row of §3.4's table with natives on, and with the float natives
/// off (the number natives on): the `rfl` theorems check, `neg (neg x) = x`
/// is proved, and the normal forms are the same terms in both modes.
#[test]
fn the_float_natives_agree_with_their_definitions() {
    let checks = float_gate::run(&[Mode::NativesOn, Mode::FloatNativesOff], Limits::default());
    let failed: Vec<String> = checks
        .iter()
        .filter(|c| !c.passed)
        .map(|c| format!("[{}] {}: {}", c.mode.name(), c.name, c.detail))
        .collect();
    assert!(failed.is_empty(), "{}", failed.join("\n"));
    // Per mode: the program, 8 natives, 13 pairs, 2 x 12 neutral witnesses
    // for `neg` and `abs`, 3 x 12 for `isNaN`, `isFinite` and `toInt`, and
    // 2 x 12 x 12 for `ieeeLt` and `ieeeLe`; then 33 + 24 + 36 + 288 normal
    // forms compared across the modes.
    assert_eq!(
        checks.len(),
        2 * (1 + 8 + 13 + 24 + 36 + 288) + 33 + 24 + 36 + 288,
        "{checks:#?}"
    );
    // The cross-mode comparisons ran.
    assert!(
        checks
            .iter()
            .any(|c| c.mode == Mode::FloatNativesOff && c.name.contains("same term as"))
    );
}

/// With every native off (the `n0` mode), `Float` can't be checked at all:
/// its proofs compute with 64-bit patterns, and without the number natives
/// `Nat.leq` and `Nat.sub` count down one `Succ` at a time. The session runs
/// out of its work budget instead of looping (a small one, so this is
/// quick).
#[test]
fn with_every_native_off_float_runs_out_of_budget() {
    let limits = Limits {
        work: 2_000_000,
        ..Limits::default()
    };
    let checks = float_gate::run(&[Mode::AllNativesOff], limits);
    let loaded = &checks[0];
    assert!(!loaded.passed, "{loaded:?}");
    assert!(loaded.detail.contains("E-RESOURCE"), "{loaded:?}");
}

/// `Float` and the definitions with float natives are the declarations the
/// kernel's float support was written for. If this fails, the library
/// changed one: check the natives in crates/core/src/float.rs still compute
/// what the definitions do, then update the hashes there to these.
#[test]
fn the_float_bindings_are_the_pinned_declarations() {
    let mut session = Session::new();
    // A binding that doesn't match fails the load; its hash is printed below
    // all the same (fix `Float`'s first: the others depend on it).
    let loaded = session.load("uses.sw", "import Std (Float)\ndef zero: Float := 0.0\n");
    let bindings = float::bindings(&session.elab.globals);
    assert_eq!(bindings.len(), 1 + float::NATIVE_HASHES.len());
    let wrong: Vec<String> = bindings
        .iter()
        .filter(|(_, actual, pinned)| actual.as_deref() != Some(*pinned))
        .map(|(name, actual, _)| format!("{name}: {actual:?}"))
        .collect();
    assert!(wrong.is_empty(), "new hashes:\n{}", wrong.join("\n"));
    assert!(loaded.is_ok(), "{loaded:?}");
}

fn loaded() -> Session {
    let mut session = Session::new();
    session
        .load("uses.sw", "import Std (Float)\ndef zero: Float := 0.0\n")
        .unwrap_or_else(|e| panic!("{e:?}"));
    session
}

/// Contract plumbing (§3.3): two primitives of the same type hash
/// differently (each hash has its operation's name), and bumping
/// `FLOAT_CONTRACT` changes each primitive's hash, and so the hash of every
/// definition that uses one (a reference is hashed as the hash it refers
/// to), which the check cache's entries list for their dependencies.
#[test]
fn primitive_hashes_have_their_operation_and_the_contract() {
    use stitchwort_core::hash::{def_hash, float_primitive_hash};
    use stitchwort_core::registry::Builtin;
    let session = loaded();
    let g = &session.elab.globals;
    let _op = g.budget.operation(Limits::default());
    let add = g.registry.loaded_def(Builtin::FloatAdd).expect("loaded");
    let sub = g.registry.loaded_def(Builtin::FloatSub).expect("loaded");
    let hash = |id| def_hash(g, id).unwrap().expect("final");
    assert_ne!(hash(add), hash(sub), "the same type, different operations");
    for id in [add, sub] {
        let now = float_primitive_hash(g, id, float::FLOAT_CONTRACT).unwrap();
        let bumped = float_primitive_hash(g, id, float::FLOAT_CONTRACT + 1).unwrap();
        assert_eq!(now, Some(hash(id)));
        assert_ne!(now, bumped);
    }
}

/// The build fingerprint, which keys both caches, changes with the Rust
/// toolchain and the target, as with the sources and `Cargo.lock` (§3.3).
#[test]
fn the_fingerprint_changes_with_the_toolchain_and_target() {
    use stitchwort_driver::fingerprint::fingerprint;
    let files = vec![("src/a.rs".to_string(), b"fn a() {}".to_vec())];
    let lock: &[u8] = b"lock";
    let base = fingerprint(Some(lock), &files, "rustc 1.99.0", "aarch64-apple-darwin");
    assert_ne!(
        base,
        fingerprint(Some(lock), &files, "rustc 1.98.0", "aarch64-apple-darwin")
    );
    assert_ne!(
        base,
        fingerprint(Some(lock), &files, "rustc 1.99.0", "wasm32-unknown-unknown")
    );
    assert_ne!(
        base,
        fingerprint(
            Some(b"other"),
            &files,
            "rustc 1.99.0",
            "aarch64-apple-darwin"
        )
    );
    assert_eq!(
        base,
        fingerprint(Some(lock), &files, "rustc 1.99.0", "aarch64-apple-darwin")
    );
}

/// `Float.ieeeEq` and `Float.compare`, natives in the runtimes only, are the
/// definitions their natives were written for. If this fails, check the JS
/// and Rust natives (crates/js, crates/rt/src/prims.rs) still compute what
/// they do, then update the hashes in crates/rt/src/natives.rs.
#[test]
fn the_runtime_float_natives_are_bound() {
    let session = loaded();
    let bindings = stitchwort_rt::natives::bind_float_natives(&session.elab.globals).unwrap();
    assert_eq!(bindings.len(), 2);
    for b in &bindings {
        assert!(b.bound, "{}: {:?}", b.name, b.hash);
    }
}
