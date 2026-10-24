//! The effect runtime (docs/proposals/effect-runtime.md §9, D1162; stage 4a).
//!
//! The library defines computations as a tree (`Effect.Comp`: `Done` and
//! `Call`) and takes them apart with four functions: `bind`, `foldComp`,
//! `translate` and `runPure`. Since stage R2 nothing else can take a
//! computation apart at run time, so generated code replaces those four with
//! the runtime here, which agrees with the tree's equations:
//!
//! - `bind c k` builds a third kind of node, `Bind`, and calls nothing;
//! - one loop, `effRun`, runs a computation, keeping the continuations of the
//!   `Bind`s it has entered on a persistent linked list (`{ k, next }`) in
//!   the heap, until the computation is `Done` with nothing pending or
//!   reaches an operation. Capturing the continuation there is keeping a
//!   pointer to the list, which is never changed, so it can be resumed any
//!   number of times, and later;
//! - a fold resumes lazily where its carrier is a computation: `k y` is
//!   `Bind (Done y) (z => fold (rest z))`, run by whoever runs the clause's
//!   result, rather than a call that runs the rest of the computation inside
//!   the clause (§9.2 of the note: sound because `handle` is the only fold
//!   that runs, and its carrier is a tree when [`Effect::carrier`] says so).
//!
//! So effectful code nests no JS call per `bind` or per operation, and a run
//! costs a constant per `bind` and per operation and handler crossed.

use std::collections::HashMap;

use stitchwort_core::registry::Builtin;
use stitchwort_core::{DataId, DefId, Globals, Term};
use stitchwort_rt::erasure::def_shape;
use stitchwort_rt::fusion::{Fused, StateFusion};

use crate::{field_key_at, js_string_literal, member, ts_key};

/// The library functions the runtime replaces.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum EffectNative {
    Bind,
    FoldComp,
    Translate,
    RunPure,
}

impl EffectNative {
    /// How many runtime parameters the definition has, which the JS below
    /// takes, one at a time.
    fn runtime_arity(self) -> usize {
        match self {
            EffectNative::Bind | EffectNative::Translate => 2,
            EffectNative::FoldComp => 3,
            EffectNative::RunPure => 1,
        }
    }

    /// The definition's JS.
    pub(crate) fn js(self) -> &'static str {
        match self {
            EffectNative::Bind => "effBind",
            EffectNative::FoldComp => "(done) => (call) => (c) => effFold(done, call, c, null)",
            EffectNative::Translate => "(m) => (c) => effTranslate(m, c, null)",
            EffectNative::RunPure => "effRunPure",
        }
    }
}

/// How a `foldComp` call's handler resumes, from the fold's carrier.
pub(crate) enum Carrier<'t> {
    /// A computation: resume lazily.
    Tree,
    /// `CompIn e t` for a row `e` that's a run-time value: a computation
    /// unless `e` is `Empty`, so the fold tests it.
    Row(&'t Term),
    /// Anything else (a plain type at the empty row, a `Delay`): resume by
    /// calling, as the tree's equation says.
    Value,
}

pub(crate) struct Effect {
    natives: HashMap<DefId, EffectNative>,
    fold: DefId,
    comp: DataId,
    /// `Effect.CompIn`, and `Effects` with its `Empty` and `Ops`.
    comp_in: Option<DefId>,
    row: Option<(DataId, usize, usize)>,
    /// Recognises state-passing handlers (stage 4d).
    fusion: Option<StateFusion>,
    runtime: String,
}

impl Effect {
    /// The runtime for `g`, if the core's effect machinery is loaded with the
    /// shapes the runtime was written for. All four functions or none: a
    /// generated `foldComp` couldn't take apart a `Bind` node.
    pub(crate) fn new(g: &Globals, counters: bool) -> Option<Effect> {
        let r = &g.registry;
        let mut natives = HashMap::new();
        for (b, native) in [
            (Builtin::Bind, EffectNative::Bind),
            (Builtin::FoldComp, EffectNative::FoldComp),
            (Builtin::Translate, EffectNative::Translate),
            (Builtin::RunPure, EffectNative::RunPure),
        ] {
            let id = r.loaded_def(b)?;
            let shape = def_shape(g, id, false).ok()?;
            let runtime = shape.mask().iter().filter(|erased| !**erased).count();
            if shape.result_erased || shape.partial || runtime != native.runtime_arity() {
                return None;
            }
            natives.insert(id, native);
        }
        let fold = r.loaded_def(Builtin::FoldComp)?;
        let comp = r.loaded_data(Builtin::Comp)?;
        let sig_map = r.loaded_data(Builtin::SigMap)?;
        let data = g.data(comp);
        if data.record || data.ctors.len() != 2 || g.data(sig_map).ctors.len() != 1 {
            return None;
        }
        let runtime_keys = |d: DataId, c: usize| -> Vec<String> {
            let ctor = &g.data(d).ctors[c];
            (0..ctor.fields.len())
                .filter(|i| !ctor.field_erased[*i])
                .map(|i| field_key_at(g, d, c, i))
                .collect()
        };
        let (done_keys, call_keys, map_keys) = (
            runtime_keys(comp, 0),
            runtime_keys(comp, 1),
            runtime_keys(sig_map, 0),
        );
        if done_keys.len() != 1 || call_keys.len() != 2 || map_keys.len() != 2 {
            return None;
        }
        let row = r.loaded_data(Builtin::Row).and_then(|d| {
            let ctors = &g.data(d).ctors;
            let empty = ctors.iter().position(|c| &*c.name == "Empty")?;
            let ops = ctors.iter().position(|c| &*c.name == "Ops")?;
            Some((d, empty, ops))
        });
        let empty_tag = row.map_or_else(
            || js_string_literal("Empty"),
            |(d, empty, _)| js_string_literal(&g.data(d).ctors[empty].name),
        );
        let count = |what: &str| {
            if counters {
                format!("effCount.{what}++; ")
            } else {
                String::new()
            }
        };
        // The same, inside an expression.
        let count_in = |what: &str| {
            if counters {
                format!("effCount.{what}++, ")
            } else {
                String::new()
            }
        };
        let runtime = RUNTIME
            .replace("@COUNTERS@", if counters { COUNTERS } else { NO_COUNTERS })
            .replace("@STEP@", &count("steps"))
            .replace("@PUSH@", &count("pushes"))
            .replace("@POP@", &count("pops"))
            .replace("@ROUTE@", &count("routes"))
            .replace("@RESUME@", &count_in("resumes"))
            .replace("@BIND_NODE@", &count_in("binds"))
            .replace("@JUMP@", &count("jumps"))
            .replace("@DONE_TAG@", &js_string_literal(&data.ctors[0].name))
            .replace("@VALUE_KEY@", &ts_key(&done_keys[0]))
            .replace("@VALUE@", &member(&done_keys[0]))
            .replace("@CALL_TAG@", &js_string_literal(&data.ctors[1].name))
            .replace("@OP_KEY@", &ts_key(&call_keys[0]))
            .replace("@REST_KEY@", &ts_key(&call_keys[1]))
            .replace("@OP@", &member(&call_keys[0]))
            .replace("@REST@", &member(&call_keys[1]))
            .replace("@INJECT@", &member(&map_keys[0]))
            .replace("@REPLY@", &member(&map_keys[1]))
            .replace("@EMPTY_TAG@", &empty_tag);
        Some(Effect {
            natives,
            fold,
            comp,
            comp_in: r.loaded_def(Builtin::CompIn),
            row,
            fusion: StateFusion::new(g),
            runtime,
        })
    }

    /// Which of the four `id` is, if any.
    pub(crate) fn native(&self, id: DefId) -> Option<EffectNative> {
        self.natives.get(&id).copied()
    }

    /// Whether `id` is `Effect.foldComp`.
    pub(crate) fn is_fold(&self, id: DefId) -> bool {
        id == self.fold
    }

    /// A fold's arguments rewritten to run as a loop with the state in a
    /// variable (`effFoldState`), if it's a state-passing handler at the
    /// empty row ([`stitchwort_rt::fusion`]).
    pub(crate) fn fuse(
        &self,
        g: &Globals,
        args: &[&Term],
    ) -> stitchwort_core::budget::Result<Option<Fused>> {
        match &self.fusion {
            Some(fusion) => fusion.fuse(g, args),
            None => Ok(None),
        }
    }

    /// The runtime's JS, to go before the generated definitions.
    pub(crate) fn runtime(&self) -> &str {
        &self.runtime
    }

    /// How a fold whose carrier (its fourth, erased, argument) is `carrier`
    /// resumes. The elaborator's carrier for `handle` is `comp_type` of the
    /// enclosing row (crates/elab/src/effects.rs): `Comp …` for a row with
    /// an ability or the closed empty row, `CompIn e t` for a bare row
    /// variable, and a `Delay` in a partial context. An empty-row variant has
    /// `CompIn Empty t` there.
    pub(crate) fn carrier<'t>(&self, carrier: &'t Term) -> Carrier<'t> {
        let (head, args) = carrier.spine();
        match head {
            Term::Data(d, _) if *d == self.comp => Carrier::Tree,
            Term::Def(id) if Some(*id) == self.comp_in && args.len() == 2 => {
                match (args[0].strip_loc(), self.row) {
                    (Term::Ctor(d, c, _), Some((row, _, ops))) if *d == row && *c == ops => {
                        Carrier::Tree
                    }
                    (Term::Var(_), _) => Carrier::Row(args[0]),
                    _ => Carrier::Value,
                }
            }
            _ => Carrier::Value,
        }
    }
}

const NO_COUNTERS: &str = "";

const COUNTERS: &str = r#"// Counts of the runtime's work, for tests (`Options::effect_counters`).
const effCount = (globalThis.__stitchwortEffectCounts ??= {
  steps: 0, pushes: 0, pops: 0, routes: 0, resumes: 0, binds: 0, jumps: 0,
  // The `run --js` runner's: operations routed, frames routing looked at,
  // and frames below the focus at each operation, summed.
  operations: 0, visited: 0, below: 0,
});
"#;

const RUNTIME: &str = r#"
// The effect runtime (docs/proposals/effect-runtime.md §9). A computation is
// `Done`, `Call` or a `Bind` node, which only this runtime builds and takes
// apart: `bind`, `foldComp`, `translate` and `runPure` are these functions.
@COUNTERS@const EFF_BIND = "$Bind";
// `bind c k`: a node, so building a long chain calls nothing.
const effBind = (c) => (k) => (@BIND_NODE@{ tag: EFF_BIND, c, k });
// The continuations pending when `effRun` last stopped at an operation.
let effPending = null;
// Runs `c` with the continuations `pending` (null, or `{ k, next }`, never
// changed once made) waiting for its result, until it's `Done` with nothing
// pending (returned) or reaches an operation: the `Call` is returned, and
// what is pending there is `effPending`.
const effRun = (c, pending) => {
  for (;;) {
    @STEP@switch (c.tag) {
      case EFF_BIND:
        @PUSH@pending = { k: c.k, next: pending };
        c = c.c;
        break;
      case @DONE_TAG@: {
        if (pending === null) return c;
        @POP@const k = pending.k;
        pending = pending.next;
        c = k(c@VALUE@);
        break;
      }
      default:
        effPending = pending;
        return c;
    }
  }
};
const effRunPure = (c) => effRun(c, null)@VALUE@;
// `foldComp done call c` with `pending` after `c`, resuming by calling:
// `k y` folds the rest at once, as the tree's equation says. For a fold whose
// carrier isn't a computation.
const effFold = (done, call, c, pending) => {
  c = effRun(c, pending);
  if (c.tag === @DONE_TAG@) return done(c@VALUE@);
  @ROUTE@const rest = c@REST@, after = effPending;
  return call(c@OP@)((y) => effFold(done, call, rest(y), after));
};
// The same, resuming lazily: `k y` is `Bind (Done y) (z => fold (rest z))`,
// which whoever runs the clause's result resumes. For a fold whose carrier is
// a computation (`handle`'s, when the row outside has an ability or is
// closed).
const effFoldLazy = (done, call, c, pending) => {
  c = effRun(c, pending);
  if (c.tag === @DONE_TAG@) return done(c@VALUE@);
  @ROUTE@const rest = c@REST@, after = effPending;
  const resume = (z) => effFoldLazy(done, call, rest(z), after);
  return call(c@OP@)((y) => (@RESUME@{ tag: EFF_BIND, c: { tag: @DONE_TAG@, @VALUE_KEY@: y }, k: resume }));
};
const effFoldCompLazy = (done) => (call) => (c) => effFoldLazy(done, call, c, null);
// A fold whose carrier is `CompIn e t`: a computation unless the row is empty.
const effFoldCompIn = (row) =>
  row.tag === @EMPTY_TAG@
    ? (done) => (call) => (c) => effFold(done, call, c, null)
    : effFoldCompLazy;
// A state-passing handler at the empty row (stage 4d, A′;
// stitchwort_rt::fusion): its operation clauses were rewritten to take
// `jump` and the state, and to end with `jump v s′` where they resumed with
// `k v s′`, so the handler runs as this loop with the state in a variable.
// A jump goes on with the rest of the computation from `v` and state `s′`,
// and calls nothing. `k` is a real resumption, for every other use of it:
// the same loop from where the operation was. `comp`: the carrier is a
// computation (the closed empty row), so the fold's result and `k`'s are
// `Done` of the state's function.
class EffJump {
  constructor(v, s) { this.v = v; this.s = s; }
}
const effJump = (v) => (s) => new EffJump(v, s);
const effStateLoop = (comp, done, call, c, pending, s) => {
  for (;;) {
    c = effRun(c, pending);
    if (c.tag === @DONE_TAG@) return done(c@VALUE@)(s);
    @ROUTE@const rest = c@REST@, after = effPending;
    const k = (y) => effStateFn(comp, (s) => effStateLoop(comp, done, call, rest(y), after, s));
    const r = call(c@OP@)(k)(effJump)(s);
    if (!(r instanceof EffJump)) return r;
    @JUMP@c = rest(r.v);
    pending = after;
    s = r.s;
  }
};
const effStateFn = (comp, f) => (comp ? { tag: @DONE_TAG@, @VALUE_KEY@: f } : f);
const effFoldState = (comp) => (done) => (call) => (c) =>
  effStateFn(comp, (s) => effStateLoop(comp, done, call, c, null, s));
// `translate m c` with `pending` after `c`: each operation renamed by `m`,
// its reply mapped back.
const effTranslate = (m, c, pending) => {
  c = effRun(c, pending);
  if (c.tag === @DONE_TAG@) return c;
  @ROUTE@const o = c@OP@, rest = c@REST@, after = effPending;
  return {
    tag: @CALL_TAG@,
    @OP_KEY@: m@INJECT@(o),
    @REST_KEY@: (x) => effTranslate(m, rest(m@REPLY@(o)(x)), after),
  };
};
"#;
