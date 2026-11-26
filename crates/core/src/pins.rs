//! The library declarations the compiler's natives were written for, each
//! pinned by its content hash (DESIGN.md §11; docs/proposals/backend-trust.md
//! §3.2, P2).
//!
//! A native computes what one particular declaration computes. If the
//! library changes that declaration's body and the native stays bound, the
//! native's answers and the declaration's own equations disagree. For a
//! native that conversion uses (the `Nat` natives, `+`'s rules) that is
//! unsound: conversion computes `Nat.sub 3 1` natively to the old answer
//! while a proof by induction over the new body proves the new one, and
//! together they prove `False`. The float natives fire only while a program
//! runs, so a stale one would make a run disagree with what was checked,
//! not prove `False`; they are pinned the same way. So a pinned
//! declaration is bound only if its content hash is the one in [`PINS`]. A
//! content hash covers the declaration's type, its body and everything they
//! refer to, so a pin on `Nat.add` pins `Nat` as well.
//!
//! A stale pin refuses the library with an `E-BUILTIN` error that names the
//! declaration and prints its new hash ([`check_def`]). Updating the pin is
//! a statement that someone has re-read the natives listed against it and
//! checked them against the changed declaration; the hash is never copied
//! from somewhere else without that.
//!
//! The kernel's natives' pins live here, beside the error that names them:
//! `crates/driver/tests/library/pinned_hashes.rs`
//! checks every pin against the whole library, and that no other 64-digit
//! hex literal hides from it. The runtimes' and JS's pins (their natives,
//! the effect natives and the rewrites) are to move here too, each listing
//! who assumes it in [`Pin::assumed_by`] (SW-1991).

use stitchwort_syntax::{Diagnostic, Span};

use crate::budget::Limits;
use crate::ev::Ev;
use crate::globals::Kernel;
use crate::hash::{data_hash, def_hash};
use crate::machine::in_kernel_modes;
use crate::registry::{Builtin, Kind};
use crate::term::{DataId, DefId};

/// Who relies on a pinned declaration meaning what it meant when the pin
/// was written.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum User {
    /// The kernel's natives and reduction rules (`native.rs`, `float.rs`,
    /// `nat_add.rs`): a stale one that conversion uses is unsound, and a
    /// stale float native makes runs disagree with checking.
    Kernel,
}

impl User {
    fn text(self) -> &'static str {
        match self {
            User::Kernel => "the kernel's",
        }
    }
}

/// A declaration and the content hash its natives were written for.
#[derive(Clone, Copy, Debug)]
pub struct Pin {
    /// The declaration: a definition or a data type (by [`Builtin::kind`]).
    pub builtin: Builtin,
    /// Its content hash, in hex, when its natives were last checked
    /// against it.
    pub hash: &'static str,
    /// What relies on it.
    pub assumed_by: &'static [User],
}

const KERNEL: &[User] = &[User::Kernel];

const fn kernel(builtin: Builtin, hash: &'static str) -> Pin {
    Pin {
        builtin,
        hash,
        assumed_by: KERNEL,
    }
}

/// Every pinned declaration.
pub const PINS: &[Pin] = &[
    // The number natives (`native.rs`); `Nat.add`'s covers `+`'s rules R3
    // and R4 too (`nat_add.rs`).
    kernel(
        Builtin::Add,
        "f3f3581f05751a4470b1254229a1905626119a6eff6ac5a241a62568d7111af1",
    ),
    kernel(
        Builtin::Sub,
        "de7069dac9dbdee5306cb3120af82b8c9829c1e6d3ee0e0a615c364954bc3a30",
    ),
    kernel(
        Builtin::Mul,
        "9106211a58e7f251e3f5b518710da1960ce95cf285a713eaa5ffa52652252aee",
    ),
    kernel(
        Builtin::Leq,
        "eea939ae65fcd686abb1096b1be7591e8de69c1fb1b21a74a72404c917684725",
    ),
    kernel(
        Builtin::EqNat,
        "32e8565001898a43e29c6a6f61fea37c5ec7d8a628d5cff66b6ea1b347132bea",
    ),
    kernel(
        Builtin::DivFuel,
        "7a01293db3c229872123c2296ce4a5fe9f833bd2cffdfa51e61859dc8adb6cee",
    ),
    // `Float`, whose `isValid` the float natives' results rely on, and the
    // float natives' definitions (`float.rs`).
    kernel(
        Builtin::Float,
        "e4ff60202ca96f2ac20c3db9d79474c8def3839c88836496a736df95675bceb7",
    ),
    kernel(
        Builtin::FloatNeg,
        "6b9065f25e9ed8b7ab713b187373075bc27453461e174698fdad670cfdb6638f",
    ),
    kernel(
        Builtin::FloatAbs,
        "fb38e6df21ff519cdfc8b7512dd5e78545994484bc7d982b903f73e71792d920",
    ),
    kernel(
        Builtin::FloatIsNaN,
        "79ba98ccc2ff711113b447f8f494d8f60a52ad7d3073ffecb925ee4f07225fe8",
    ),
    kernel(
        Builtin::FloatDecEq,
        "6ff801d851b5fdc26df7cf6321ab1652c9850b8028262d78581706f91046504a",
    ),
    kernel(
        Builtin::FloatIsFinite,
        "16540775350f744d0f0ed958df5191b2bf9accc0e0db79731ff8c5656f910787",
    ),
    kernel(
        Builtin::FloatIeeeLt,
        "6a9574474272226699bc08034b905e8e3416cdbe65491f8778d113dcd2036b0b",
    ),
    kernel(
        Builtin::FloatIeeeLe,
        "06c93fa67525bdff3f19579c82798b569db55bba61604b8d6f017edcf10fc7f3",
    ),
    kernel(
        Builtin::FloatToInt,
        "333b00241e0d3551d40c53d39c1aed97abdd4d2298d8924ee8b5d49d8ece285d",
    ),
    kernel(
        Builtin::FloatAdd,
        "283d0bd4c74364bb03a1c48cdbb569545e62cce80d6884702488e62c03470bd3",
    ),
    kernel(
        Builtin::FloatSub,
        "e32ec974e18c8e4b3c2ed96fca7272de475154d0a1f1fbe0cec54a0a7df99793",
    ),
    kernel(
        Builtin::FloatMul,
        "1c14bb71c22ca038f46fd38055dcd63d69eaad1068992237db538578e7475849",
    ),
    kernel(
        Builtin::FloatOfInt,
        "71dd0caa52db12a81286738b5ecae596725079de9649e7521421bb9a7d40733a",
    ),
    kernel(
        Builtin::FloatOfNat,
        "2c26ac2d06133e9bcc97153fb288c2af8466b4d7388c7b609526dc373a78327e",
    ),
    kernel(
        Builtin::FloatDiv,
        "dfcf26fbadad31fdab8e7cfe4627a5f6caa40589c87f588d38b8bef4b3ab09c6",
    ),
    kernel(
        Builtin::FloatRem,
        "387d3f084d23e01108222382d0a99297436730618eed1b8de8124933ae3ba15e",
    ),
    kernel(
        Builtin::FloatFloor,
        "865a1f53b12faa343f3b6b3eda0a9a4aa1a3b225d7404b1febab02715928fbcf",
    ),
    kernel(
        Builtin::FloatCeil,
        "38b3f0d39e48d1ddd56e9f41b880bea18dd0f00a346140df4f752370ed7f3e0c",
    ),
    kernel(
        Builtin::FloatTrunc,
        "2310fceb3acb6f9b5c3503b895b3beb69559e02220fdb8516cd9d1b137faa69c",
    ),
    kernel(
        Builtin::FloatRound,
        "dc3f8e77ad612502190913dff50f4e1fa1a405387d5ba074349f195ef91ff6c0",
    ),
    kernel(
        Builtin::FloatSqrt,
        "184d3e4b2dd2fe29a89d92cc93513c7662e11b6eabba18d4b86b15e3d26fbfa5",
    ),
];

/// The pin on `b`, if it has one.
pub fn pin(b: Builtin) -> Option<&'static Pin> {
    PINS.iter().find(|p| p.builtin == b)
}

/// Hashes, with an operation running for the hasher's depth guard. `None`
/// for a declaration that isn't final, or that ran out of stack.
fn hex(
    g: &Ev,
    f: impl FnOnce() -> crate::budget::Result<Option<crate::hash::ContentHash>>,
) -> Option<String> {
    let _op = g
        .machine
        .budget
        .operation(Limits::stack_only(Limits::default().stack));
    f().ok().flatten().map(|h| h.hex())
}

/// The content hash definition `id` has now. `None` for a theorem whose
/// proof hasn't been checked ([`crate::globals::Def::unproved`]), which has
/// no full hash: never the pinned declaration.
pub fn def_hex(g: &Ev, id: DefId) -> Option<String> {
    if g.def(id).unproved() {
        return None;
    }
    hex(g, || def_hash(g, id))
}

/// The content hash data type `d` has now.
pub fn data_hex(g: &Ev, d: DataId) -> Option<String> {
    hex(g, || data_hash(g, d))
}

/// Whether definition `id`, bound as `b`, is the declaration `b`'s pin was
/// written for. `false` if `b` has no pin.
pub fn holds(g: &Ev, id: DefId, b: Builtin) -> bool {
    pin(b).is_some_and(|p| def_hex(g, id).as_deref() == Some(p.hash))
}

/// Whether data type `d`, bound as `b`, is the declaration `b`'s pin was
/// written for. `false` if `b` has no pin.
pub fn holds_data(g: &Ev, d: DataId, b: Builtin) -> bool {
    pin(b).is_some_and(|p| data_hex(g, d).as_deref() == Some(p.hash))
}

/// Whether definition `id`, bound as `b`, is pinned and isn't the pinned
/// declaration: for a test session that lets such a definition run as
/// written, without its native.
pub fn stale_def(g: &mut Kernel, id: DefId, b: Builtin) -> bool {
    in_kernel_modes(g, |g| pin(b).is_some() && !holds(&g.ev(), id, b))
}

/// The check made where a builtin is bound (`bind_builtin_def` and
/// `bind_builtin_data` in the elaborator), for every builtin with a pin, so
/// that a pin is checked whether or not the registration function for its
/// builtin remembers to. The registration functions check as well, so the
/// kernel's guard doesn't depend on the elaborator.
pub fn check_bound_def(g: &mut Kernel, id: DefId, b: Builtin) -> Result<(), Diagnostic> {
    if pin(b).is_none() {
        return Ok(());
    }
    #[cfg(feature = "test-bypass")]
    record_bound_check(b);
    in_kernel_modes(g, |g| check_def(&g.ev(), id, b))
}

/// [`check_bound_def`] for data type `d`, bound as `b`.
pub fn check_bound_data(g: &mut Kernel, d: DataId, b: Builtin) -> Result<(), Diagnostic> {
    if pin(b).is_none() {
        return Ok(());
    }
    #[cfg(feature = "test-bypass")]
    record_bound_check(b);
    in_kernel_modes(g, |g| check_data(&g.ev(), d, b))
}

#[cfg(feature = "test-bypass")]
thread_local! {
    /// Whether [`BOUND_CHECKS`] records on this thread. Off unless a test
    /// starts it, or `STITCHWORT_RECORD_BOUND_CHECKS` is set, so a
    /// long-running session (the language server) doesn't keep every check.
    static RECORDING: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
    static BOUND_CHECKS: std::cell::RefCell<Vec<Builtin>> = const { std::cell::RefCell::new(Vec::new()) };
}

/// `STITCHWORT_RECORD_BOUND_CHECKS`, read once: whether [`BOUND_CHECKS`]
/// records from a session's first check.
#[cfg(feature = "test-bypass")]
static RECORD_FROM_ENV: std::sync::OnceLock<bool> = std::sync::OnceLock::new();

/// Adds `b` to [`BOUND_CHECKS`] while recording.
#[cfg(feature = "test-bypass")]
fn record_bound_check(b: Builtin) {
    let on = RECORDING.get()
        || *RECORD_FROM_ENV
            .get_or_init(|| crate::env_flag::env_flag("STITCHWORT_RECORD_BOUND_CHECKS"));
    if on {
        BOUND_CHECKS.with(|c| c.borrow_mut().push(b));
    }
}

/// The builtins [`check_bound_def`] and [`check_bound_data`] have checked on
/// this thread since the last call, and starts recording them: for the test
/// that every pin is reached by the check at binding.
#[cfg(feature = "test-bypass")]
#[doc(hidden)]
pub fn take_bound_checks() -> Vec<Builtin> {
    RECORDING.set(true);
    BOUND_CHECKS.with(|c| std::mem::take(&mut *c.borrow_mut()))
}

/// Refuses definition `id`, bound as `b`, unless it is the declaration
/// `b`'s pin was written for. A builtin with no pin is refused too: a
/// native is only ever bound through a pin.
pub fn check_def(g: &Ev, id: DefId, b: Builtin) -> Result<(), Diagnostic> {
    debug_assert_eq!(b.kind(), Kind::Def, "{b:?}");
    check(g.def(id).span, b, || def_hex(g, id))
}

/// [`check_def`] for data type `d`, bound as `b`.
pub fn check_data(g: &Ev, d: DataId, b: Builtin) -> Result<(), Diagnostic> {
    debug_assert_eq!(b.kind(), Kind::Data, "{b:?}");
    check(g.data(d).span, b, || data_hex(g, d))
}

fn check(span: Span, b: Builtin, now: impl FnOnce() -> Option<String>) -> Result<(), Diagnostic> {
    let Some(pin) = pin(b) else {
        return Err(Diagnostic::error(
            "E-BUILTIN",
            format!(
                "internal error: `{}` has a native but no pin in crates/core/src/pins.rs",
                b.name()
            ),
        )
        .with_label(span, "here"));
    };
    let now = now();
    if now.as_deref() == Some(pin.hash) {
        return Ok(());
    }
    Err(stale(span, pin, now.as_deref()))
}

/// The error for a pinned declaration whose content hash is now `now`.
fn stale(span: Span, pin: &Pin, now: Option<&str>) -> Diagnostic {
    let users: Vec<&str> = pin.assumed_by.iter().map(|u| u.text()).collect();
    let name = pin.builtin.name();
    let d = Diagnostic::error(
        "E-BUILTIN",
        format!(
            "the library's `{name}` isn't the declaration {} natives were written for",
            users.join(" and ")
        ),
    );
    match now {
        Some(now) => d
            .with_label(span, format!("its content hash is now {now}"))
            .with_note(format!(
                "if this change was meant, check each native that assumes `{name}` against it, \
                 then update its pin in crates/core/src/pins.rs to \"{now}\""
            )),
        None => d.with_label(span, "its content hash can't be computed"),
    }
}

/// Every pin, with the content hash its declaration has in `g` now (`None`
/// if it isn't loaded): for `task pins:show` and the test that checks every
/// pin against the whole library.
pub fn table(g: &Ev) -> Vec<(&'static Pin, Option<String>)> {
    let registry = g.env.registry();
    PINS.iter()
        .map(|p| {
            let now = match p.builtin.kind() {
                Kind::Data => registry.loaded_data(p.builtin).and_then(|d| data_hex(g, d)),
                _ => registry.loaded_def(p.builtin).and_then(|id| def_hex(g, id)),
            };
            (p, now)
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn each_declaration_is_pinned_once() {
        for (i, a) in PINS.iter().enumerate() {
            assert!(
                PINS[i + 1..].iter().all(|b| b.builtin != a.builtin),
                "{:?} is pinned twice",
                a.builtin
            );
            assert!(
                a.hash.len() == 64
                    && a.hash
                        .bytes()
                        .all(|c| matches!(c, b'0'..=b'9' | b'a'..=b'f')),
                "{:?}'s pin isn't a hash",
                a.builtin
            );
        }
    }

    #[test]
    fn every_native_is_pinned() {
        for n in crate::native::Native::ALL {
            assert!(pin(n.builtin()).is_some(), "{n:?}");
        }
    }

    #[test]
    fn a_stale_pin_names_the_declaration_and_its_new_hash() {
        let now = "0".repeat(64);
        let e = check(Span::NOWHERE, Builtin::Sub, || Some(now.clone())).unwrap_err();
        assert_eq!(e.code, "E-BUILTIN");
        assert!(e.message.contains("`Nat.sub`"), "{}", e.message);
        let text = format!("{e:?}");
        assert!(text.contains(&now), "{text}");
        assert!(text.contains("crates/core/src/pins.rs"), "{text}");
        let fine = pin(Builtin::Sub).unwrap().hash.to_string();
        assert!(check(Span::NOWHERE, Builtin::Sub, || Some(fine)).is_ok());
    }

    #[test]
    fn an_unpinned_builtin_is_refused() {
        let e = check(Span::NOWHERE, Builtin::Div, || None).unwrap_err();
        assert!(e.message.contains("no pin"), "{}", e.message);
    }
}
