# The effects pre-pass's cost on nested code

**Status:** draft 1, 26 November 2026. Ticket SW-4889, from SW-4885's
measurements. Recommends option B below, an optimisation with results
unchanged (the orchestrator's call under D3447); option C is a separate
design question, Matt's, and is not recommended for this problem.

## 1. The problem

Checking `f (f (… 0))` takes quadratic time: 141 / 582 / 2,392 ms at
1,000 / 2,000 / 4,000 levels (SW-4885, release CLI, measured). Steps grow
linearly (13 a level); the guard's visits grow as about n²/2 (6,292 /
22,542 / 85,042 / 330,042 at depths 100 / 200 / 400 / 800, for a
monomorphic `f` and for `same : a -> a` alike). A profile at 5,500 levels
puts about 98% of busy samples in `effects::call_performs` and what it
calls.

## 2. What the pre-pass is for

`effects::may_perform_at` (effects.rs) answers, from the syntax and what
is known of the names in it, whether elaborating an expression may
perform operations: it calls an operation or an effectful function with
enough arguments, or contains `;`, `handle`, or a `let` whose value or
rest may. Lambda bodies don't count, and neither does a part that goes to
a parameter of computation type (it is passed, not run). The answer
decides *how* an expression is elaborated, before any of it is:

- `check_special` (check.rs, before checking a plain value) and
  `infer_inner`: a yes sends the expression to `pure_first` (plain calls
  first, for bare rows) and then `run_pure` (computation mode in the empty
  row); a no elaborates it as a plain value.
- Computation mode (`comp_check_in`, `sequence`, `comp_call`,
  `passed_args`, about 25 sites in effects.rs): which arguments are run
  first and bound, which are values.
- `performs_only_in_bare_rows` (the same walk with `bare_rows_pure` set),
  `no_effect.rs`'s `W-NO-EFFECT`, and the lambda and `let` inference sites
  in check.rs.

It is syntactic because computation mode has to know, before elaborating
the head, that the arguments are to be sequenced with `bind`.

The quadratic: `check_special` asks it of every expression checked. For
`f a`, `call_performs` asks `may_perform` of `a`, which for `a = f b`
asks of `b`, and so on to the bottom: n nodes. Then checking `a` against
`f`'s parameter type calls `check_special` on `a`, which walks n-1 nodes
again. Every computation-mode site re-asks the same way, so an effectful
chain is quadratic too (not measured).

What the answer reads, all of which a reuse must account for: the local
context (`head_type` reads local types and local definitions; dot calls
read `written` types; a match narrows local types; a `let`'s rest is asked
once without its name in scope and again with it); metavariable solutions
(a local of type `?T` reads as "doesn't perform" until `?T` is solved to
`{E} Nat`; a parameter type `?P` reads as "not passed" until solved to a
computation type, so solutions can turn either answer into the other);
the abilities declared so far, whether a description's recursion is in
scope, and `bare_rows_pure` (all three already in `PerformsKey`); and,
for a list, tuple or record literal, the expected type.

## 3. Options

**A. A stamped "doesn't perform" passed to the argument's check.** When a
call's walk finds an argument doesn't perform, the call's check tells the
argument's check, which skips its own walk. *Cost:* small if it is a
one-shot slot in `Ctx` taken by the next `check_special`. *Invariant:* the
argument is checked in the caller's context (application arguments bind
nothing) and no metavariable existing at the walk has been solved since.
*Growth:* a one-shot slot carries only the direct argument's answer, so
the grandchild walks again: every other level walks, still n²/4. To be
linear it must carry the answers for every node the walk visited, which
is option B. *End state:* not one; a special case of B.

**B. A memo of the walk's answers, keyed by expression and context.**
`may_perform_at` records the answer for each node it visits (both yes and
no) and consults the memo on entry. Key: the expression's address, a
*context identity*, `bare_rows_pure`, the abilities' count and the
recursion flag; literals asked against an expected type
(`performs_by_expected`) aren't memoised. Each entry carries a
*metavariable stamp*: the store's `meta_epoch`, the number of
metavariables and the trail's length when it was recorded. An entry is
used only if the epoch is unchanged (nothing taken back) and every
solution on the trail since was of a metavariable made since (the walk
can only have read older ones). The memo is per declaration, cleared with
the rest of the declaration state.

- *Context identity:* a `u64` on `Ctx`, fresh (from a counter) on every
  binding pushed and every wholesale change of `types`, `scope`, `env` or
  `locals` (the case-tree narrowings in families.rs, matching.rs and
  lib.rs, auto.rs's obligations), and carried in `Mark` so that `reset`
  restores it. A pop followed by a different push gets a new identity, so
  equal lengths never pass for equal contexts. A `let`'s rest asked
  before and after its name is bound, and the same arm body checked in
  two case-tree leaves, fall out as different keys with no special rule.
- *The metavariable test in O(log n):* an append-only record, beside the
  trail, of the positions where the solved metavariable's number reaches
  a new minimum counted from the end (a monotonic stack); "the smallest
  number solved since position t" is a binary search. A linear scan of
  the trail since the stamp would be quadratic again for `same`, whose
  check solves a fresh `?a` at each level.
- *Cost:* the context identity is the bulk: `Ctx`'s binding fields are
  public and pushed or replaced directly at about 70 sites in 20 files.
  Make them private behind methods that keep the identity; mechanical,
  and the compiler finds every site. Then the stack, the memo and its
  key: about 100 lines. Estimate: one Sonnet lane for the refactor (or
  DeepSeek, it is a sweep), one Opus lane for the memo, an hour or two
  each in agent time.
- *Invariant (result-preserving):* a hit returns exactly what the walk
  would compute now, because every input the walk reads is either in the
  key (context, flags, the literal exclusion) or covered by the stamp
  (metavariables), and global tables (names, definitions' types, the
  `performs` cache's final definitions) don't change within a
  declaration. Results, messages and hashes are then unchanged; only
  visits fall. The lane must audit the read set (`dot::target`,
  `defaults::of_name`, `named::reached`, `decode`) against the key, and
  ship a shadow mode (`STITCHWORT_SHADOW_MEMO=1`: on each hit, recompute
  and panic on a difference) for Overmind to run over the examples, std
  and AoC once before the memo is trusted.
- *Growth:* the root's walk visits the n nodes once and records them;
  each nested `check_special` then hits in O(log n). Linear visits
  (estimated), and the computation-mode sites, which go through the same
  function, get the same. Estimated elaboration at 4,000 levels: under
  200 ms, from 2,392 ms. The stack limit (about 6,000 levels on a 64 MiB
  stack, SW-4885) is untouched; it is the check's own recursion.
- *End state:* yes for this problem, as long as the pre-pass exists.

**C. Decide effects from elaborated types.** Elaborate arguments first
and bind those whose type turns out to be a computation in the current
row, as a coercion would; no syntactic walk. *Cost:* a redesign of
computation mode, `pure_first`/`run_pure`, bare rows (D1123, D1124) and
the passed-argument rule (D1140), with new answers where the syntax and
the types disagree today (an argument whose type is still `?T` when it is
checked, a call whose head's type is found only by elaborating it).
Elaboration order, terms and messages would change, and so would which
programs elaborate. *Invariant:* none; it is a different language
mechanism. *Growth:* linear, as elaboration is. *End state:* arguably the
principled one (one source of truth, the types), but it is a large
design change in its own right, not justified by this cost alone, and
would need its own note and Matt's decisions.

**D. Narrower variants considered and dropped.** Memoising only "doesn't
perform" saves the probe but leaves effectful chains quadratic, for the
same complexity. Keying by lengths of the context instead of an identity
is unsound (a pop and a different push give equal lengths; two leaves of
a case tree check one arm body at equal lengths with different types). A
"pure spine" flag set while checking a call known not to perform is
wrong for arguments passed to computation-typed parameters, which the
walk skipped and which may perform. Recording only on the binder-free
spine and scoping entries to the recording check's lifetime avoids the
context identity but needs its own argument for every context change
inside that check; the identity is simpler to trust.

## 4. Recommendation

Option B, in two lanes: first the `Ctx` refactor (private binding fields,
context identity in `Mark`), then the memo with the metavariable stamp,
the shadow mode and a test that pins linear growth: SW-4885's probe
(`resources.rs`, visits at depths 100 to 800) turned into an assertion
that visits at 800 are under five times those at 200 (quadratic growth
gives 16 times), for both `f` and `same`, and one effectful chain. It is
an optimisation with results, messages and hashes unchanged, so the
orchestrator's call under D3447, with its performance-log entry (D3444).
The shadow-mode run is what stands behind "unchanged". Option C stays
open as a design direction if computation mode is ever revisited for its
own reasons.
