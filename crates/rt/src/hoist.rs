//! Closed signature maps, built once (docs/proposals/effect-runtime.md
//! §9.9, stage 4f; shared by both backends).
//!
//! Wherever code calls a function whose row is smaller than its own, the
//! elaborator wraps the call in `translate m`, `m` a `SigMap` that renames
//! the callee's operations into the caller's row: `sigCase sigLeft
//! sigFromNo`, say. Such a map is usually closed (it reads no variable at
//! run time), but generated code built it again on every call: inside a
//! loop, once per element, and a `translate` keeps its map alive for as long
//! as a continuation that crosses it is pending, so a search's every
//! pending choice kept its own copy of the same map. The backends instead
//! build a closed map once, at its first use, and keep it (a JS module
//! variable, a constant of the machine).
//!
//! Only maps are hoisted: their values are small (two closures), so
//! keeping one for the rest of the run costs nothing, and building one
//! has no effect to repeat or skip. A closed application of anything else
//! is left where it is, since hoisting an arbitrary closed term (a long
//! `List.range`, say) would keep its value alive for the whole run.

use stitchwort_core::registry::Builtin;
use stitchwort_core::{DataId, DefId, Globals, Term};

use crate::erasure::def_shape;

/// Recognises a closed application of a function to a `SigMap`.
pub struct SigMaps {
    sig_map: DataId,
}

impl SigMaps {
    /// `None` if the core's effect machinery isn't loaded.
    pub fn new(g: &Globals) -> Option<SigMaps> {
        Some(SigMaps {
            sig_map: g.registry.loaded_data(Builtin::SigMap)?,
        })
    }

    /// Whether definition `id` applied to `args` is a whole application
    /// (every parameter supplied) whose result is a `SigMap`, and reads no
    /// variable at run time: built from definitions, constructors and
    /// literals alone, wherever its arguments aren't erased. A definition
    /// without runtime parameters (`sigId`) is a constant already.
    pub fn closed_map(&self, g: &Globals, id: DefId, args: &[&Term]) -> bool {
        let def = g.def(id);
        if args.len() != def.arity || !self.returns_map(&def.ty, args.len()) {
            return false;
        }
        let Ok(shape) = def_shape(g, id, false) else {
            return false;
        };
        shape.runtime_arity() > 0 && runtime_closed_app(g, id, args)
    }

    /// Whether `ty`, under its first `n` parameters, is `SigMap …`.
    fn returns_map(&self, ty: &Term, n: usize) -> bool {
        let mut ty = ty.strip_loc();
        for _ in 0..n {
            match ty {
                Term::Pi(_, _, _, body) => ty = body.strip_loc(),
                _ => return false,
            }
        }
        matches!(ty.spine().0, Term::Data(d, _) if *d == self.sig_map)
    }
}

/// `id` applied to `args` reads no variable at run time: its erased
/// arguments aren't looked at.
fn runtime_closed_app(g: &Globals, id: DefId, args: &[&Term]) -> bool {
    let Ok(shape) = def_shape(g, id, false) else {
        return false;
    };
    if shape.partial || shape.result_erased {
        return false;
    }
    let mask = shape.mask();
    args.iter()
        .enumerate()
        .all(|(i, a)| mask.get(i).copied().unwrap_or(false) || runtime_closed(g, a))
}

/// `term` reads no variable at run time. Conservative: a lambda, a `let`
/// or a match counts as reading one.
fn runtime_closed(g: &Globals, term: &Term) -> bool {
    let (head, args) = term.spine();
    match head {
        Term::Def(id) => runtime_closed_app(g, *id, &args),
        Term::Ctor(_, _, params) if args.is_empty() => params.iter().all(|p| runtime_closed(g, p)),
        Term::Nat(_) | Term::Chars(_) if args.is_empty() => true,
        _ => false,
    }
}
