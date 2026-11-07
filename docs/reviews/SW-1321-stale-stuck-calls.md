# Audit: stuck calls read after their unknown was solved

**Ticket:** SW-1321, following SW-1315 (D2585). **Reviewer:** Opus, by reading only: nothing
built or run, 7 Nov 2026. **Checked against:** `lane/SW-1321` at `246731117` (= `main`). Line
numbers are from that commit. Every repro below is **not run**.

## The gap, in one paragraph

A definition's case tree that meets an unsolved unknown stops and returns the call as it was,
`Neutral(Def f, args)` (`stuck_tree`, `core/src/value.rs:1985`). Nothing in that value says which
unknown it waits on. `force` (`value.rs:581`) replaces a solved unknown only at a value's head,
and a glued call (`Value::Call`) only by its kept unfolding. So once the unknown is solved, the
stuck value stays stuck until someone reads it back and evaluates it again. Reading it back puts
the solution in, so messages print what it should compute to (SW-1315's "two sides that look
equal"). Applying a stuck call to one more argument does run its tree again
(`apply_step`, `value.rs:939`, `Control::Unfold`). Matching on it, projecting it or comparing it
doesn't. Each site that cares has to refresh on its own, and some don't.

## Summary

| # | Site | Decides | Stale form seen? | Consequence | Confidence |
|---|------|---------|------------------|-------------|------------|
| F1 | `unify.rs:1150` `stale_within` | whether a failing pair is evaluated again (SW-1315) | yes: an unknown inside a constructor argument (`f [?b]`, `f (?b, c)`, `f (Some ?b)`) isn't looked for | wrong failure (user-visible error) | high |
| F1b | `unify.rs:1223` `blocked_within` | whether a failing pair is put aside (`Task::Later`) | same blind spot for *unsolved* unknowns in constructor arguments | wrong failure where a later pair would have solved it | high |
| F2 | `core/src/value.rs:124` `Kept::fits`, used by `force_now` (`:591`) and `force_call` (`:975`) | whether a glued call's kept unfolding is still good | yes: the epoch counts solutions **taken back**, not solutions **added**, so an unfolding kept while stuck is served after its unknown is solved | every `force` of a shared call sees the stale form. In `unify` SW-1315's check rescues direct arguments. Elsewhere (tactics, `dot`, `cases`, `conv`) it doesn't | high (the mechanism); medium (how often it bites) |
| F3 | `unify.rs:1540` same-head stuck calls | compares the spines, in shortcut mode | yes: two stale calls of one definition whose arguments differ but whose values agree (`pick ?b 0` against `pick ?c 0`, `?b := True`, `?c := False`) | wrong failure: the failing pair is an argument pair (`True` against `False`), which isn't stale, so the whole pair is never evaluated again | medium |
| F4 | `unify.rs:2353` `rename`, `Neutral(Head::Def)` arm | occurs and scope checks while building a solution | yes: a stale call's spine can mention the unknown being solved, or a variable out of scope, that computing it would drop | wrong failure of `solve`, though `first_order` sometimes rescues it | medium (mechanism); low (frequency) |
| F5 | `queue.rs:905` `tactic_or_wait`, first run; `ring.rs:118` and `:929`; `rewrite.rs:738`; `cases.rs:1347` | the goal a tactic works on | yes: only a *resumed* tactic re-evaluates its goal (`queue.rs:938`) | `ring` sees `pick True x` as an atom distinct from `x`. `rewrite`'s goal term keeps an unreduced redex. `cases`'s finder sees a solved scrutinee and finds nothing to split. When no pending unknown is left, the error is shown | medium |
| F6 | `dot.rs:112-119` `unfold`, from `view_start` (`:270`) | where to look up `.field` | yes: a receiver type stuck on a since-solved unknown is taken as "as unfolded as evaluation could make it" | `E-…` "can't look up" error (`blocked`, `dot.rs:983`) on a type that computes to a data type | high (mechanism); low (frequency) |
| F7 | core `conv` called from the elaborator (~25 sites) | definitional equality without solving | yes, by design: it compares unknowns by number and never re-evaluates (`check.rs:670`'s doc). `Ctx::conv_now` is the refreshing version and has 3 callers | wrong "different" only. Most sites are a first try followed by unification or a refresh; a few aren't (listed below) | medium |
| F8 | `named.rs:116` `signature`'s `stuck` | whether named arguments meet a type stuck in a definition | yes | the "stuck" path for a function type that computes to a `Pi` | low |

No site gives a **wrong success**. A stale form is a less computed version of the true value.
Every rule that answers "equal" on stuck forms (same head and equal spines, equal case trees,
constructor fields, eta) is a congruence, so it holds for the computed values too. Proof
positions stay safe: a stale spine still holds the solved unknown itself, so `may_mention_meta`
(`unify.rs:1186`) is true and the arguments are compared in shortcut mode (U3). The kernel would
catch a wrong success in any case. It checks the zonked terms with `NoMetas` (epoch 0), where
nothing can be stale (`crates/core/src/check.rs`, through `value::conv`).

## Helpers that refresh, and who uses them

- **`force`** (`value.rs:581`): the head only, a solved unknown or a call's kept unfolding
  (F2). Everything starts with it, and it isn't enough on its own.
- **`force_solved`** (`value.rs:616`): a solved unknown at the head, applied to its spine; stops
  at a glued call. Used by `meta_against_call`, `all_unknown_arguments`, `unknown_argument`,
  `rename`, `matches_at_once` and `dot::step_value`. Head only, like `force`.
- **`unify::afresh`** (`unify.rs:1133`): `eval(quote_folded(v))`. Used by `Task::Later`
  (`:283`) and SW-1315's `stale` path (`:259`).
- **`unify::stale`** (`unify.rs:1146`): the cheap test for "a call stuck on a solved unknown",
  three calls deep, direct arguments and `k +` only (F1).
- **`interfaces::refresh`** (`interfaces.rs:1409`): zonk, then evaluate. Used by `tri`,
  `attempt`, `cases.rs:696`, `Ctx::conv_now`.
- **`Ctx::conv_now`** (`check.rs:676`): `conv`, then, if the trail isn't empty, both sides
  refreshed and compared again. Used at `cases.rs:667` and `:1030`.
- **`omega::recomputed`** (`omega.rs:2418`): quote, evaluate, and keep the result if it got
  further. Used before an `Int` or `Nat` atom is made (`:2065`, `:2165`). `ring` has nothing
  like it.
- **Resumed checks** evaluate afresh with `eval(quote_folded(…))`: `Comparison::resume`
  (`queue.rs:1117`), `WaitingTactic::resume` (`:936`), `WaitingMatch::resume`
  (`matching.rs:840`). The first run of each isn't refreshed (F5).
- **The metavariable epoch** (`MetaStore::meta_epoch`, `state/metas.rs:81`) goes up only in
  `metas_taken_back`. Within an epoch, solutions are only added, and the trail only grows.
  `unify::effects` (`unify.rs:1060`) keys the call memo by `(epoch, trail length, postponed)`,
  which does see new solutions. `Kept` (F2) and `TreeMemo` key by epoch alone. That's right for
  `TreeMemo`, which keeps only "equal", and wrong for `Kept`.

## Details

### F1, F1b: unknowns inside constructor arguments (`unify.rs:1150`, `:1223`)

`stale_within` looks at each `Elim::App` argument of the stuck call. It counts the argument if
it's a solved unknown (or `k +` one), and it recurses into an argument that is itself a call.
`blocked_within` does the same for unsolved ones. A case tree with nested patterns gets stuck
on a field of an argument, though: `match bs with | [True, ..rest] => …` on `[?b]` is stuck on
`?b`, which sits inside `Cons ?b Nil`. Neither function looks there. List, pair and option
patterns are everywhere in AoC code, so this is the realistic case.

- F1: the pair fails although evaluating again would make it equal.
- F1b: the pair fails at once instead of waiting as `Task::Later`, so SW-896's "solve it from
  a later pair, then compare again" doesn't happen for these.

**Repro (not run)**, `examples/accept/solved-after-stuck-nested.sw`, in SW-1315's shape:

```
import Std (Bool, Nat)

def pickHead (bs: List Bool): Nat → Nat :=
  match bs with
    | [True, .._] => n => n
    | _ => n => 0

theorem lem [b: Bool]: b = b ∧ pickHead [b] 5 = pickHead [b] 5 := Both rfl rfl

theorem picked: True = True ∧ pickHead [True] 5 = 5 := lem
```

`pickHead [?b]` is forced when applied to `5`. It gets stuck on `?b` inside the list, and the
application gives `Neutral(pickHead, [[?b], 5])`. The first conjunct solves `?b`. The second
compares the stale call with `5`. `stale` sees a constructor and a number, and says no.

**Fix.** Give both functions the bounded walk `may_mention_meta` already does (into `Ctor`
fields, `Data` arguments, `NatAdd`, nested calls, at most `MENTION_LOOK` parts), testing for a
solved or an unsolved, unfrozen unknown. One shared walker with a predicate keeps them in step.
SW-1315's "three calls deep" becomes "64 parts". A false positive costs one `afresh`, which is
bounded, so the walk can be generous.

**Test:** the accept example above, plus a `blocked` twin where the second conjunct comes
*before* the one that solves `?b` (`pickHead [b] 5 = pickHead [b] 5 ∧ b = b`), which needs
F1b. `task test:one -- solved-after-stuck`, plus `snap:hashes` for the new example.

### F2: a kept unfolding outlives the solution it was stuck on (`core/src/value.rs:124`)

`Kept::fits` accepts a kept unfolding if its epoch is 0 or the current one (and the modes
match). The epoch changes only when solutions are taken back. So: a glued call `F ?b` is forced
while `?b` is unknown, its unfolding is stuck on `?b` and is kept, and then `?b` is solved. Every
copy of that call (they share the `Rc<Unfolding>`) still forces to the stuck value: `force_now`
returns it, since a `Neutral(Def)` doesn't "need forcing" (`needs_forcing`, `:1796`). Before
SW-1782 the unfolding was kept unconditionally. SW-1782 covered retractions, but never
additions.

Calls are forced while their unknowns are still open all the time: `blocked_within` forces every
argument it inspects (`:1235`), and so do `one_step_apart`'s `same_outer_layer` and `on_pending`.
Context types (`cx.types[l]`) and a tactic's `expected` are long-lived copies.

In the unifier, SW-1315's `stale` rescues this. It forces the call (stale), sees the solved
direct argument, and `afresh` reads the call back folded, which gives a new `Call` with a new
cell. Everywhere else the forced value is stale: `ring`/`omega`/`rewrite`/`cases` (F5), `dot`
(F6), `conv` (F7), `named` (F8), and `one_step_apart`'s outer-layer test (low; see "Checked").

**Repro (not run)**, a sketch. It needs a call forced while its unknown is open, then the same
value used by a site without a refresh:

```
def pick (b: Bool): Nat → Nat := match b with | True => n => n | False => n => 0
theorem pickBoth [b: Bool] (x: Nat) (p: b = True ∧ pick b x = x): pick b x = x := p.2
theorem use (x: Nat): pick True x = x :=
  let h := pickBoth x (Both rfl ring)
  h
```

`p`'s type is built with `?b` open, so `pick ?b x` is stuck. `rfl` solves `?b`, and `ring` then
gets the stale `pick ?b x`. This shows F5 more than F2. A pure F2 repro needs a glued call
(arity reached, no further application) forced early. Whoever implements it should build one
with a unit test in `crates/core` (a `Value::Call` forced, then a solution added, then forced
again), rather than through the surface language.

**Fix.** Add to `Metas` a count that only grows within an epoch: the trail length, which
`unify::effects` already uses (`fn solutions(&self) -> usize`, 0 for `NoMetas`). Record it in
`Kept`. In `fits`, accept a kept value whose count differs only if it can't change with more
solutions: anything but `Neutral(Head::Def(_) | Head::Quot(_), _)`. A constructor, data type,
number or variable application is final at its head. Only a stuck call needs computing again.
This costs one compare per force of a call. It may move hashes where an elaborated term changes
from a stuck call to its value (migration cost never counts).

**Test:** a core unit test in `value.rs`'s tests (they already build a `Metas` in
`value.rs:4466`). Then `task test:one -- solved-after-stuck` and the `bound_to_the_prelude`
extract tests (a std-core-adjacent change).

### F3: two stale calls of one definition (`unify.rs:1540`)

In the same-head arm of `unify_step` for stuck `Neutral(Def)`s, `blocked` is false for stale
calls (their unknowns are solved), `may_mention_meta` is true, and the argument pairs are pushed
in shortcut mode. The arm returns `true`, so `run` never asks whether the *pair* is stale. If an
argument pair then fails, that failing pair is `True` against `False`, which isn't stale.

**Repro (not run):**

```
def pick (b: Bool): Nat → Nat := match b with | True => n => n | False => n => 0
theorem lem [b c: Bool] (h: pick b 0 = pick c 0): b = b ∧ c = c ∧ pick b 0 = pick c 0 :=
  Both rfl (Both rfl h)
theorem use (h: 0 = 0): True = True ∧ False = False ∧ pick True 0 = pick False 0 := lem h
```

This depends on elaboration order: `h` is checked against `pick ?b 0 = pick ?c 0` after the
result type has solved `?b` and `?c`. If the result is unified first, the stale pair is the third
conjunct of the statement itself (`pick ?b 0` against `pick ?c 0`, read from `lem`'s type and
the expected type). In the expected type those compute to `0`, so then it isn't triggered. Low
confidence that this exact file shows it.

**Fix:** at the top of the same-head arm, if `stale(a) || stale(b)`, push
`Values(afresh(a), afresh(b))` and return. Once F1's walk is in place, that is the same test.

### F4: `rename` on a stale call (`unify.rs:2353`)

`rename` writes a stuck `Neutral(Def)` as its head applied to the renamed spine. A stale spine
can mention the unknown being solved (occurs) or a variable outside its scope, where the
computed value wouldn't: `pick ?b y` with `?b := False` is `0`. Glued calls already have a
fallback: they're written as the call, and on `Fail::No` they're unfolded (`:2299-2324`). Stuck
neutrals don't.

**Repro:** not easily written at the surface: the unknown being solved must stand in the stale
call's dead branch. Better as a unit test in `unify.rs`'s tests, which build values by hand
(`meta`, `with_first`).

**Fix:** in the `Neutral(Head::Def)` arm, on `Fail::No`, if `stale(value)`, rename
`afresh(value)` instead (once).

### F5: a tactic's first run takes its goal as it is (`queue.rs:905`)

`tactic_or_wait` runs `ring`, `omega`, `rewrite` and `cases` on `expected` unchanged. Only a
resumed run evaluates it afresh (`:938`). If the first run fails and `search_pending_in` finds no
pending unknown (it zonks, so it sees the solution, not the stale call), the error is final.
Each tactic, on a stale goal:

- `ring` (`ring.rs:118` `force`, atoms `:929`): `cx.quote(value)` reads `pick True x`, an atom
  distinct from `x`. The "left over" error follows. `ring` knows about staleness only in its
  final check (`:1277`).
- `omega`: covered by `recomputed` for atoms. Fine, as far as I can see.
- `rewrite` (`rewrite.rs:738-739`): `cx.quote(&goal_value)` keeps the unreduced redex in
  `goal_term`, so the occurrence search sees `pick True x` where the goal means `x`. A rule for
  `x` may find nothing. Rule premises are already read again (`:492`, `:588`).
- `cases` (`cases.rs:1347`, the finder's `walk`/`chain`): the stale call's scrutinee forces to
  the solution, a constructor, so the finder finds nothing to split, or says the goal is stuck
  on something else. Only hypothesis lookup refreshes (`:696`).

**Repro (not run):** the `pickBoth … (Both rfl ring)` file under F2. A `cases` twin:
`pickBoth x (Both rfl (cases))` with `pick` on a `Nat` argument, so there's something to split.

**Fix:** in `tactic_or_wait`, evaluate `expected` afresh before the first run whenever the
attempt's trail is not empty (`eval(quote_folded(expected))`, as `WaitingTactic::resume`
does). That's one read-back per tactic, small next to the tactic itself. It's simpler than
"retry on failure", and every tactic sees one goal shape on its first and its resumed runs.
`ring_goal` could then drop its fallback at `:1279`.

**Test:** the accept example; `task test:one --` the ring, rewrite and cases examples that use
`tactic_or_wait` (`task test:lane AREA=tactics`, if that area exists).

### F6: `.field` on a receiver whose type is stale (`dot.rs:112-119`)

`step_value` maps a `Neutral(Def F)` type to `TyHead::Def(F)` with no way to unfold, and
`unfold` returns `None` for any value ("A value is already as unfolded as evaluation could make
it"). That is exactly the assumption that fails here. The lookup ends in `blocked(…)` at
`dot.rs:983`. `view_start` (`:270`) takes `rty` as inferred.

**Repro (not run):**

```
def Box (b: Bool): Type := match b with | True => Nat | False => Bool
def mk [b: Bool] (same: b = True) (x: Box b): Box b := x
theorem use: Nat := (mk rfl 3).succ
```

It depends on `mk rfl 3`'s type being computed (as `Box ?b`) before `rfl` solves `?b`. With
the usual left-to-right order it is: the result type `Box ?b` is evaluated when `mk` is applied
to `?b`, before the explicit arguments. Medium confidence.

**Fix:** in `unfold`, for `None | Some(Ty::Value(v))` with a stuck `Neutral(Def)`, try
`eval(quote_folded(v))` once, and go on if it gave something else. Or refresh `rty` in
`view_start` when the trail isn't empty.

### F7: core `conv` from the elaborator

`value::conv` is the kernel's: it doesn't refresh. In the elaborator it is a cheap first try
almost everywhere, and a wrong "different" is the worst it does. Sites I read:

- Fine (a first try followed by something that sees solutions): `omega.rs:271` (falls back on
  the search), `cases.rs:687/699` (then `refresh`, `:696`), `interfaces.rs:690` (both sides are
  `cx.eval` of terms, so fresh), `ring.rs:947` and `omega.rs:2376` (after `matching::same` on
  quoted terms, which carry solutions), `dot.rs:265`.
- May give a user-visible wrong "different": `cases.rs:1035`, `:1051` and `:1054`, the premise
  lookup against `cx.types[k]`, which may be stale (the goal side was refreshed, the hypotheses
  not). Also `cases.rs:929`.
- Not read: `congruence.rs:552`, `derive*.rs`, `equations.rs:2815/4426/6169`, `partial.rs`,
  `lib.rs:2163`, `shared.rs:177`, `data_auto.rs:211`, `interfaces.rs:762`, `cases.rs:903`. Most
  compare declared types, which hold no unknowns.

**Fix:** a sweep that replaces `conv` with `cx.conv_now` where either side may predate a
solution, and leaves a comment where `conv` stays on purpose.

### F8: `named::signature` (`named.rs:116`)

A function type that is a stale stuck call gives `open: false, stuck: true`. Named arguments
then go down the "stuck" path (`named.rs:305`, `:469`, `:504`) instead of seeing the
parameters. Rare: the function's type must be computed by a definition matching on an unknown
solved since. D1115 means a solved unknown at the *head* ends the walk on purpose. That rule is
about naming, not this, so a refresh is consistent with it. **Fix:** fold into F2 and the design
note (D2603) rather than patch alone.

## Recent changes

- **Record eta** (`Elim::Proj`, call fields). `stale_within` and `blocked_within` skip `Proj`
  eliminations and test the call's `App` arguments, which is right for a field of a call.
  Forcing a call field consults the base's kept cell and the field's own (`force_call`,
  `:975-1003`), so F2 applies to both. Rule 1 (`unify.rs:1632`, `!blocked(n)`) on a stale `n`
  compares field by field against projections of the stale value, and each field pair gets the
  `stale` rescue. That's sound and only as weak as F1. No new path beyond F1 and F2.
- **Bounded read-back** (`quote_at_most`, folded). Used by `on_pending` and `mentions_unknown`;
  it puts solutions in. Fine.
- **SW-1782** (`Kept` epochs and modes): it made the kept unfolding safe against solutions taken
  back, but it doesn't notice new ones (F2). The mode checks have no stale-stuck aspect.

## Checked and fine

- `run`'s `Task::Later` (`unify.rs:282`): evaluates both sides afresh. Its first branch (nothing
  solved since) can't be stale relative to when it was put aside.
- `meta_against_call` (`:2158`): `force_solved` on both sides. It decides only "an unsolved
  unknown against a glued call", and solving with the call as written is right whatever the
  call's unfolding is.
- `one_step_apart` (`:1727`): `same_outer_layer` on forced values can see a stale kept
  unfolding (F2). It may then take the lazy-delta path where the outer layers would agree. That
  path solves only through `same_arguments`, gives a genuine solution and is documented as
  "kept". Low; F2 removes it.
- `all_unknown_arguments`, `unknown_argument` (`:1780`, `:1795`): `force_solved` per argument.
- `same_arguments_solving_nothing` and the SW-1506 shortcut (`:1295`): "different" there only
  skips a shortcut; the unfoldings are compared afterwards.
- Unifier `CallMemo` (`call_key`, `record_different`): keyed by `effects`, which includes the
  trail length, so a new solution files under a new key.
- `TreeMemo` (`value.rs:3517`, `MemoKey`): remembers only "equal", by epoch; adding solutions can't
  undo an equality.
- `conv`'s own `CallMemo` (`value.rs:2848`): lives within one `conv`, which solves nothing.
- `same_stuck_trees` (`value.rs:3370`): `walk_tree` forces each scrutinee from the
  environment, so a solved unknown scrutinee is taken; the stuck scrutinees and the leaves go to
  `same`, which in the unifier is `unify_in` with its `stale` rescue.
- `plus_rule`, `stuck_sum` (`:832`, `:864`): `force` per argument, so a solved one isn't
  "unknown"; `mentions_unknown` reads solutions in.
- `first_order` (`:1997`): a solution built from a stale spine is still a solution (it's
  evaluated and solves the equation), just possibly a different one.
- `on_pending`, `sets_aside`, `note_unfilled`: reached only after the `stale` check in `run`;
  they read back with solutions.
- `type_of`, `apart`, `form`, `rigid_head`: types and rigid heads don't depend on whether a call
  is stale.
- `matches_at_once` (`value.rs:682`): `force_solved` on the scrutinised argument.
- `queue::head_meta`, `ready` (`queue.rs:1205`): head only. A stale `needs` counts as ready, and
  the resume refreshes.
- `matching::blocker` (`matching.rs:752`): zonked terms.
- `interfaces::attempt`, `tri`, `stuck_on_found`: `refresh` first. `locals` (`:1282`) forces
  only the head of a hypothesis type to see an interface, and a stale stuck type computing to an
  interface is far-fetched (low).
- `omega`'s atoms: `recomputed` (`omega.rs:2418`).
- `rewrite`'s rule types and premises: read again (`rewrite.rs:492`, `:588`).
- `zonk`, `zonk_call`, `refold`: start from terms, so nothing is stale.
- The kernel: `NoMetas`, epoch 0, nothing to be stale on.

## Tickets to file

1. **Unifier: `stale` and `blocked` look inside constructor arguments** (F1, F1b; with F3 as the
   same test applied in the same-head arm). Opus (unifier, D2506). Est. 60 min.
2. **Core: a kept stuck unfolding is computed again after a new solution** (F2: `Metas` gains a
   solutions count, `Kept::fits` checks it for stuck values). Opus (core). Est. 60 min.
3. **`tactic_or_wait` evaluates the goal afresh before the first run** (F5; `ring`, `rewrite`,
   `cases`). Sonnet. Est. 45 min.
4. **`.field` on a receiver whose type is stuck on a solved unknown** (F6). DeepSeek, from the
   repro (a bounded elaborator fix with a clear goal), Sonnet as fallback. Est. 30 min.
5. **`rename`: a stuck call on a solved unknown is evaluated again before an occurs or scope
   failure** (F4). Opus (unifier). Est. 45 min.
6. **Sweep the elaborator's `value::conv` calls; `conv_now` where values may predate a
   solution** (F7; `cases.rs:929/1035/1051/1054` first). Sonnet. Est. 45 min.
7. **Design note: stuck values that say what they wait on** (D2603). Opus. Est. 90 min.

## Questions for Matt

- **D2603: fix the sites one by one, or design a systemic fix?** Every finding here has the same
  cause: a stuck call doesn't record the unknown it's stuck on, so `force` can't tell that it
  would now compute. Making that systemic is a core value change: record the blocking unknown
  when a case tree gets stuck, and have `force` run the tree again once it's solved, as
  `apply_step` already does for one more argument. That is what the elaboration-zoo's glued
  evaluation and Lean's "stuck on mvar" do. It would remove the need for `stale`, `afresh` in
  `run`, `recomputed`, `refresh` in many places, and the resume-time re-evaluations.
  **Recommendation:** both, in order. Tickets 1-3 now: they're small, and they cover the cases
  most likely in AoC code (list and pair patterns, tactics after `Both rfl …`). Ticket 7 as a
  proposal in `docs/proposals/`, before more sites get their own refresh. Tickets 4-6 wait for
  its outcome, as the design would make them unnecessary.
