# SW-2208: review of merge `3f07b1aa7` (SW-2030, a `match`'s equation in a `decreasing` body)

A review of stage 2 of `docs/proposals/decreasing-with-hypothesis.md`. I
only read code: no builds and no runs. Read: `git show 3f07b1aa7 -m
--first-parent`, all of `crates/elab/src/decreasing/plain.rs`, and the
changed parts of `decreasing.rs` (`FOUND`, `arms_call_itself`, `Active`,
the pipeline around `plain_view`, `decreasing_step`, `lifted_helper_body`,
`in_scope`). In `matching.rs`: `lifted`, `variable`, the equation binding
in `bind_generalised` and `in_arms`'s unused-name rule. In `lift.rs`:
`draft_with`, `spine`, `captures`, `passable_lets`, and the helper loop
around `lifted_helper_body`. Also `logic.rs` (`tag_plain`, `settle_tagged`
and its `keep_plain` read), `with_local_retries`, `rewind_globals` and its
callers, the kernel's `Eq` rule, `opaque_helper`, the new accept and reject
examples and their snapshots, the hash snapshots that changed
(`decreasing`, `prelude`), `std/List/Unfold.sw`, 2024 day 23's
`largestFrom` and `Proofs/Search.sw`, and the guide and `syntax.md`
changes. I didn't repeat SW-2145's findings
(`docs/reviews/SW-2145-decreasing-plain-if.md`), which SW-2164 is fixing
now. Where stage 2 changes one of them, I say so.

## Summary

The change is sound, and it's well made. It trusts nothing new.
`H.%plain` is an ordinary definition, and the kernel proves
`H.%plain.%same` equal to `H`. So `f.%plain` is provably the step, and
`f.unfold` is a true theorem whatever the twins contain. The only thing
that can go wrong is that `f.unfold` shows less than it could, or a
generator gap gives an internal error. I found no new shape that reaches
an internal error. The twin path through `mark`, `post`, `pre`, `part` and
`hole_proof` is consistent: a `%twin` mark is placed only where `part` or
`hole_proof` can reach it, and `post` and `hole_proof` use the same arity
and `unadapt` checks that `mark` made. Two design facts make the
over-approximating name check harmless. A lifted helper captures only the
variables it uses (`lift.rs`, `captures`), so an equation no proof uses is
never one of `H`'s parameters. And a proof `let` (erased type) isn't
passed to an inner helper but re-created in it, so the outer `let` really
is dead. The stage 1 hash snapshots back this up: across std, only
`List.unfold` (a named `match e:`) gained a twin, and every other
`decreasing` definition's terms are unchanged.

The main risk is outside this diff. SW-2164, running now, adds a
kept-count check (SW-2145 F7) and a fallback (D3100). Both must know
about twins: `count` includes `%twin` marks, and the fallback runs after
twins have been declared. Stage 2 also widens SW-2145 F1. Plain `if`s
inside lifted `match`es now keep their tags, so an F1 shape inside a
`match` arm, which used to compile, now gives the internal error. The
rest is small: a `let` that stays in `f.unfold` after an inner twin drops
its only use, calls in a pattern guard that the name check misses, a
stale-record guard that works but whose stated cause doesn't occur, and
test gaps. The biggest gap is a nested `match` (a twin calling a twin),
which nothing tests.

**Top five recommendations**

1. Tell SW-2164 now: its count check must count `%twin` marks as well as
   `%plain` tags, its fallback must deal with twins already declared, its
   `keep_plain` rework must cover `lifted_helper_body` (which resets the
   flag where it should restore it), and its F1 tests should include an F1
   shape inside a `match` arm (F2). S.
2. Add tests: a nested `match` whose inner arm calls `f` (twin calling
   twin), a dropped `let` in the examples (today only AoC covers it), an
   equation used outside a proof (kept), two scrutinees, a `match` under
   a lambda with its `f.unfold` form pinned, and a lexicographic measure
   (F3). S-M.
3. Run `dead_lets` again after `post`, so a `let` used only by an argument
   an inner twin drops goes too, along with anything only it mentions
   (F1). S.
4. Scan the pattern guards as well as the arm bodies in
   `arms_call_itself` (F4). S.
5. Make `tagged_helpers` exact (remove an entry when a helper's body has
   no tags), keep the guard as a check, and correct its comment. Limit
   `twin()` to lifted `match`es (F6, F7). S.

## Findings

| # | Severity | Confidence | Where | What | Size |
|---|---|---|---|---|---|
| F2 | medium | high | SW-2164's scope; `plain.rs:455`, `decreasing.rs:1471-1492` | SW-2164's count check, fallback and `keep_plain` rework must know about twins; stage 2 widens SW-2145 F1 into `match` arms | S |
| F3 | medium | high | `examples/accept/decreasing-match-fact.sw` | a nested `match` (twin calling twin), a dropped `let`, a kept equation, two scrutinees, under-a-lambda and lexicographic cases are untested | S-M |
| F1 | low | medium | `plain.rs:1001-1004` | `dead_lets` runs before `post`, so a `let` whose only use is an argument an inner twin drops stays in `f.unfold` | S |
| F4 | low | high | `decreasing.rs:67-83` | the name check reads `alt.body`, not `alt.guard`; a call through a local alias or on an aliased scrutinee gets no equation and no hint | S |
| F5 | low | medium | `matching.rs:1352-1365`, `plain.rs:1012-1016` | the unnamed equation is visible to every proof in the arm; one that isn't a decrease proof keeps it in `f.unfold` | S (doc) |
| F6 | low | medium | `plain.rs:932-939`, `decreasing.rs:1485-1490` | the stale-record guard is right and sufficient, but the map is never cleaned, and the cause its comment names (a retry) doesn't reuse ids | S |
| F7 | low | low | `plain.rs:926-968`, `decreasing.rs:1093` | `twin()` is tried for every definition in the helper range that has a `%rec` binder, local `def`s and abandoned attempts' helpers included | S |
| F8 | low | high | `decreasing.rs:67`, `plain.rs:1026-1028` | performance: the name check runs eagerly and re-walks nested arms; twins are made for helpers only ever called under a lambda, and nothing uses them | S |
| F9 | low | high | comments, `syntax.md` | one wrong reason in a comment; a slightly overstated module doc; the note when there are several `%found`s | S |

## Details

### F2. SW-2164 must know about twins (medium, high confidence)

SW-2164 is implementing SW-2145's lane A on a branch that includes this
merge. Its brief was written from SW-2145, before stage 2 existed. There
are four interactions:

- **The count check (SW-2145 F7).** That recommendation was to "count the
  `%plain` `let`s in `marked` … unless there are exactly `count` of them,
  each the decision of an `elim`". Stage 2's `mark` increments `count` for
  each twin call too (`plain.rs:455`) and marks it `let %twin := Refl in
  call`, not as a `%plain` tag. A check that counts only `%plain` would
  fail on every definition with a twin, which today includes `List.unfold`,
  and every stage-2 definition would then fail or fall back. The check
  has to count both: `%plain` lets in an `elim`'s decision, plus `%twin`
  lets around a call of a known twin with `twin.arity` arguments.
- **The fallback (D3100).** `plain_view` declares and defines the twins
  (`plain.rs:879-884`) before it builds `f.%plain`. If `f.%plain`'s
  generation fails and SW-2164 falls back to the old `f.unfold`, the twins
  are already in the kernel. They're harmless, but `made` must still get
  them (for `def_items`, as SW-2145 F6 notes for `%unfoldStep`), or they
  must be left out deliberately. As things stand, an `Err` from
  `plain_view` drops the `twins` vector it filled.
- **`keep_plain` (SW-2145 F5).** `lifted_helper_body`
  (`decreasing.rs:1471-1492`) sets `keep_plain` to true and then to
  false. It doesn't restore the previous value. If it ever ran inside the
  step's `finish` window, where the flag is true, it would turn the flag
  off for the step's final settle, and the step's plain `if`s would lose
  their tags. That costs the plain view, not correctness. SW-2145 found
  no lift during `finish`, so this is latent. If SW-2164 replaces the
  `Cell` with a parameter to the final settle, `lifted_helper_body` should
  take the same parameter (always "keep" there), so the two can't drift
  apart.
- **F1's reach.** Before stage 2, a helper's body was settled stripped, so
  a tagged `if` inside a `match` arm just became `if _:` in `f.unfold`.
  Now helpers keep their tags (`lifted_helper_body`) and go through `mark`
  (`twin` → `plain_def`). So SW-2145 F1's two shapes inside a `match`
  arm, which compiled before stage 2, now give the internal error. SW-2164's
  fix lives in `mark`, so it covers helpers automatically. Its tests
  should include one F1 shape inside an arm, for example `climbBoth`'s
  body under `match n - i with | Succ _ => …`.

**Recommendation.** The orchestrator sends these four points to SW-2164
before it finishes. No new lane is needed.

### F3. Test gaps (medium, high confidence)

The example's theorems can fail. `countUpEnds` and `drainGrows` match on
the scrutinee after `rewrite f.unfold`, and `drainEmpty`, `drainStep` and
`drainBelowOver` rewrite it. With an `rfl` still in `f.unfold`, all of
them would hit `E-MATCH-MOTIVE`. The `*Unfolds` theorems are weaker: the
old form would probably convert too, since both sides get stuck on the
same neutral case. So the stage's core claim is tested. These aren't:

- **A nested `match`**, an inner `match` in an outer one's arm with the
  call in the inner arm. This is the "calls a twin itself" path: `mark` in
  the outer helper finds the inner twin, and `twin()` relies on the
  `*d >= h` id order (`plain.rs:942-947`) with the callee lifted first. If
  the order were ever reversed, the outer helper would quietly get no
  twin. The example has no nested `match`.
- **A dropped `let`** (`dead_lets`). Only 2024 day 23's `let fewer` covers
  it, and lanes don't run AoC by default. Add a `drain` variant with
  `let fewer := Set.sizePopMin …` and a `drainStep`-style theorem.
- **An equation the body uses outside a proof**, such as a record's proof
  field. It must be kept, and `f.unfold` then shows it.
- **Two expression scrutinees**, `match a.popMin, b.popMin with`, which
  bind two `%found`s.
- **Under a lambda.** `syntax.md` documents that a `match` inside a
  function passed to another keeps its equation in `f.unfold`, but
  nothing pins that form (SW-2209 will change it).
- **A lexicographic measure** with a `match` fact.
- **The reject note's other forms**: a named `match` (no "(this `match`'s
  arm)" line), and an aliased scrutinee (F4).

**Recommendation.** Add these to `decreasing-match-fact.sw`, with
`*Step`-style theorems where a proof generalises or rewrites, and a
reject example for the guard case of F4. Update the hash snapshot. S-M.

### F1. A `let` an inner twin no longer needs stays (low, medium confidence)

`plain_def` runs `dead_lets` on the adapted tree, then marks it, then
takes `post` (`plain.rs:1001-1004`), and computes `needed` from `post`
(`1012-1016`). `post` can remove uses that were there before: a twin's
call drops the arguments its twin doesn't take. So a `let` whose only use
was such an argument survives `dead_lets` and stays in `H.%plain` (or
`f.%plain`) as a dead `let`. Anything its value mentions is still
`needed`.

Proof `let`s aren't affected. An erased `let` isn't passable
(`lift.rs:1381-1397`), so the inner helper re-creates it and the outer
`let` is already dead. That covers 2024 day 23's `let fewer` and almost
every real case. What remains is a data `let` used only by an inner
call's decrease proof, such as `let bound := rest.size` mentioned only in
`[decreasing := omega [...]]`. `f.unfold` then shows a `let bound := …`
that nothing uses. That's cosmetic, and conversion still matches the
user's restatement. If the data value itself mentions the equation, the
equation is `needed`, and the `rfl` comes back. An example is a subtype
value built with `found`. That case is contrived.

**Answer to question 4:** no `let` the plain body needs can be dropped.
`dead_lets` drops only `let`s whose body doesn't mention them, and the
later steps (`mark`, `post`, `reindex`) never add a mention. `post`
replaces a tagged `elim` by `ite b` with `b` taken from the tag, and a
twin call by a call on a subset of its arguments. The error goes the
other way: a `let` can be kept that isn't needed.

**Fix.** `let post = dead_lets(g, &l.post(g, &marked)?)?;`. The `%same`
proof still proves `pre(marked) = post(marked)`, and the twin's body is
zeta-equal to that, so the kernel's conversion accepts it. Add a nested
`match` test with a data `let`. S.

### F4. What the name check misses (low, high confidence)

`arms_call_itself` (`decreasing.rs:67-83`) scans `free_names_of(&alt.body)`
for the definition's last name segment, as a name or a dot method. It
over-approximates, and that's harmless. An equation no proof uses isn't
captured (`lift.rs`, `captures` takes the least closed set), so `H`
doesn't take it and nothing changes, as the unchanged std hashes show.

It misses three things:

- **A call in a pattern guard**, `| Some (l, rest) if total rest > 0 =>
  …`. `ast::Alt` keeps the guard in `alt.guard`, which isn't scanned.
- **A call through a local alias** that doesn't share the name, such as a
  `let` bound to a partial application of `f` before the `match`.
- **An aliased scrutinee** (`let p := s.popMin; match p with`). This one
  is deliberate: `alias.is_none()` (`matching.rs:535`).

**Answer to question 3:** when it misses, the `match` has no equation,
exactly as before stage 2. The call's obligation fails with
`E-DECREASING` and lists what else is in scope. Since no `%found` is
there, it doesn't add the "name it" note, but the general note
(`[decreasing := …]`) still shows. The user writes `match found:` and
it works. It fails closed and nothing unsound gets through.

**Fix.** Scan `alt.guard` too. For the aliased scrutinee, a
`with_note` in `in_scope` when a `match` on a `let` alias encloses the
call would be enough, but it isn't worth a separate change. S.

### F5. The unnamed equation reaches every proof in the arm (low, medium confidence)

`%found` is bound with `cx.bind` (`matching.rs:1352-1365`), so it's in
scope for every `auto` and `omega` in the arm, not only the decrease
proofs. If one of those other proofs uses it, for example `xs.get j
[inBounds := omega]` in `match n - k with | Succ j => …`, then `H`
captures it, `post` still mentions it (only recursive calls lose their
proofs), and `f.unfold` shows `H'` with the equation and its `rfl`. A
program that compiled before stage 2 could then find its existing
`f.unfold` proofs hitting `E-MATCH-MOTIVE`. That needs `omega` or `auto`
to pick the new fact over the route it used before. The lane's whole-AoC
run (0 errors) shows it doesn't happen today. This is SW-2145 F3's
pattern for `match`. Under a lambda the same thing happens by design,
which `syntax.md` says, and SW-2209 picks it up.

**Recommendation.** Add one sentence to `syntax.md`: the equation is
there for any proof in the arm, and if a proof other than the call's uses
it, `f.unfold` shows it. Binding `%found` for decrease obligations only
would change D2870's "`auto` and `omega` see it like any other", so I
wouldn't. S.

### F6. The stale-record guard (low, medium confidence)

**Answer to question 5.** The guard (`plain.rs:932-939`) uses a record
only if settling it gives exactly the kernel's body for that id.
That's right and it's enough. If the stripped forms are the same term,
the record is a tagging of this very body, and the kernel checks
everything built from it anyway. So a wrong record could cost an internal
error at worst, never soundness.

Is it needed? Records are keyed by `DefId` and live for the whole
`decreasing_step`. They're inserted only when the tagged and stripped
bodies differ (`decreasing.rs:1485-1490`), and never removed. A record
goes stale only if an id is reused for a different body while `Active`
is set. That doesn't happen through `with_local_retries`, the "abandoned
attempt" the comment names: it doesn't rewind the kernel, so a retry's
helpers get new ids. It can happen through `rewind_globals`
(`equations.rs:2471`, `induct.rs:356`) if an on-demand equation is
generated mid-body, lifts a `match` while `Active` is set, and is then
rewound. That would be rare, but a cheap check against it is reasonable.

**Recommendation.** Make the map exact. When the bodies don't differ,
`remove(id)` the entry. Then the guard is purely an invariant check, and
it can stay. Change the comment to name the real cause, a kernel rewind
reusing an id. S.

### F7. `twin()` isn't limited to lifted `match`es (low, low confidence)

`helpers` is every definition from `first_helper` to the end of the
kernel (`decreasing.rs:1093`). `twin()` builds a twin for any of them
that has a body and a `%rec` parameter. That includes a local `def`
lifted from the body (which `tables.lifted` doesn't list), and helpers
from an attempt that `with_local_retries` abandoned after lifting, since
their ids aren't rewound. A local `def` that captures `%rec` and takes a
proof parameter would get `go.%plain`. Then `f.unfold` would show that
instead of the local definition its local equations are about. I didn't
find a `decreasing` body with a local `def` that calls the outer
definition, so this is a reading, not a reproduction. `respects` has
always iterated the same range.

**Fix.** In `twin()`, return `None` unless `lifted` (already computed,
`plain.rs:957-959`) is `Some`. S.

### F8. Performance (low, high confidence)

- `arms_call_itself` runs for every `match` elaborated while `Active` is
  set, before `lifted` knows whether any scrutinee is an expression
  (`matching.rs:468`). Each nesting level re-walks all the arms below it,
  so the cost is quadratic in nesting depth. Compute it lazily, on the
  first expression scrutinee with no name.
- `lifted_helper_body` settles every helper twice, and `twin()` settles
  the record a third time for the guard. These are linear passes over
  bodies that are already in memory, so they're fine. I note them only
  because together they triple the settling for `decreasing` helpers.
- A helper called only under a lambda gets a twin and a `%same` that
  nothing uses: `mark` never marks those calls, so `count` stays 0 and
  `f.%plain` may not be made at all. That's two dead definitions per such
  `match`, each with a copy of the case tree.

### F9. Comments and docs (low, high confidence)

- `arms_call_itself`'s doc says "an unused one costs nothing, since
  `f.unfold` leaves it out". The real reason is that the helper doesn't
  capture it (`lift.rs`, `captures`), so `H` never takes it. That matters
  to a reader, because the twin isn't what makes it free.
- `plain.rs`'s module doc says "`let`s only the dropped proofs used go
  too". That's true at one level, not through a nested twin (F1).
- `in_scope` labels each `%found` "(this `match`'s arm)". With two
  scrutinees, or nested `match`es, the label is ambiguous. Saying the
  scrutinee instead ("(the arm of `match set.popMin`)") would read better.
  Tiny.
- `syntax.md`'s new bullet says a `match` inside a function passed to
  another "keeps its equation in `f.unfold`". That happens only when a
  proof used the equation. Otherwise the helper doesn't take it. Add
  "if a call's proof used it".

## Answers to the brief's questions

1. **Soundness and trust.** Sound. Twins and their lemmas are kernel
   definitions and theorems, and `f.unfold`'s statement is still built
   from the plan (`decreasing.rs`, `decreasing_unfold`). `%found` is an
   ordinary equation hypothesis with an `Eq` over any type
   (`core/check.rs:359`). `H'` is transparent, as `H` and `f.%step` are
   (`opaque-definitions.md` §6.4). Nothing in the generated terms is
   accepted without the kernel checking it.
2. **Marking and building agree for twins.** Yes, in the shapes I traced.
   A `%twin` mark is placed only at an allowed position, which is the
   same set `part` and `hole_proof` reach: a leaf, an `if` branch, a root
   `let`'s body, an application's head or argument, a constructor field,
   or an annotation. `post` and `hole_proof` both go through `twin_of` and
   `unadapt`, with the arity and the `%rec` form `mark` already checked.
   An over-applied helper is marked at its exact-arity prefix, which
   `part`'s `App` case reaches. The arguments are marked with `allowed =
   false`, so no tag or mark survives inside them, apart from SW-2145 F1's
   unmarked type arguments. I found no new user shape that gives an
   internal error. The one regression is F1's reach into arms (F2).
3. **The name check.** It misses calls in guards and through aliases. A
   miss means no automatic equation and an ordinary `E-DECREASING`, which
   naming the `match` fixes (F4).
4. **Dropped `let`s.** None the plain body needs. One can be *kept* that
   isn't needed (F1).
5. **The stale-record guard.** Right and sufficient. It's needed only
   against a kernel rewind reusing an id, not a retry. Make the map exact
   and keep the guard as a check (F6).
6. **Tests and docs, day 23.** The core claim is tested by theorems that
   can fail. The nested `match` and the other gaps aren't (F3). The docs
   are accurate apart from F9's two phrases, and the guide's snippet is
   checked. 2024 day 23's change is sound. The removed `if fewer:` was
   always true (`Set.sizePopMin`), so its `else best` was dead and the
   function's values are unchanged. `fewer` and `withinOthers` are proofs
   and are erased, so the run is unchanged too. `largestStep`'s statement
   is unchanged (only its last arm's proof is now `rfl`), and the lane's
   AoC check ran clean.

## Checked and sound

- **The equation's binding.** `%found` is added only for an expression
  scrutinee with no name and no `let` alias, after the motive is built,
  just as a written name would be. A variable scrutinee is untouched
  (`variable` runs first). `in_arms` treats `%found` as unnamed, so there's
  no unused-name warning. `%` can't be written, so no source can refer to
  it.
- **Over-approximation is free.** Because captures are least sets, an
  unused `%found` isn't a parameter, a helper with no `%rec` gets no twin,
  and terms don't change. That fits the snapshots: in std, only
  `List.unfold` (a named `match e:` whose `e` only the proof uses) changed.
- **The twin's telescope.** `needed` is closed under the types of kept
  parameters, with `%rec`'s plain type (`plain_rec`), so `new_level`'s
  `unwrap_or(0)` is never reached for a kept type. The `%same` statement
  covers all of `H`'s parameters, with `%rec` as `y… p => r y…`. The
  proof's left side unfolds `H` and sees that adapter literally, because
  `Rec::adapt` makes exactly the form `unadapt` reads.
- **`hole_proof` for a twin call.** `H.%same` at the call's own arguments,
  with `r` for the adapter, has the type `pre(call) = post(call)` by
  construction, so the J chain's step is right.
- **A tagged `if` whose fact only reaches a twin's dropped argument.**
  `mark`'s `unused` reads the branch as `post` has it, so the `if` is
  kept, and `Decidable.elimIf` or `Bool.elimDecTrueIf` gets `sy : h → pre
  = post`. `post` doesn't mention `h`, so `t Trivial` is `post`.
- **Order of twins.** `helpers` runs in id order, and an inner `match` is
  lifted (and declared) before the outer one that calls it, so its twin
  exists when the outer one is marked. A helper that refers to itself or
  to a later one in its group gets no twin. That's safe, since it's
  called as `H` with the adapter. (Untested: F3.)
- **`dead_lets`** keeps every `%`-named `let`, so `%plain` tags and
  `%conj` survive. It runs before `%twin` marks exist. Dropping a `let` is
  zeta-equal, and the kernel's conversion bridges it.
- **The `E-DECREASING` note** appears only when a `%found` is in scope, and
  the reject snapshot shows the intended three notes.
- **The 1 Nov review** (`docs/research/rust-codebase-review.md`) has no
  findings in `decreasing/`, `matching.rs`'s `lifted` or `lift.rs`'s helper
  bodies. `docs/research/architecture-review.md` only places `decreasing`
  in the equations area, which is unchanged in its point (inputs are
  tables written during the body check).

## Calls I made

- F5: document that the equation is visible to every proof in the arm,
  rather than limiting it to decrease proofs (D2870 already says `auto`
  and `omega` see it like any other fact).
- F6: keep the guard, make the map exact.
- F2: deliver it as a message to SW-2164, not a lane.
- No D questions. Everything here is implementation or test scope.

## Tickets to file

**Message to SW-2164 (orchestrator, now):** F2's four points (count
`%twin` marks, twins under the fallback, `lifted_helper_body` and
`keep_plain`, an F1 test inside a `match` arm).

**Lane A (Opus, about 45 min, after SW-2164; same files, proof
generation): stage 2 hardening.**
- F1: `dead_lets` after `post`, plus a nested-`match` test with a data
  `let`.
- F6: remove the record when a body has no tags, and fix the comment.
- F7: `twin()` only for lifted `match`es.
- F4: scan `alt.guard` in `arms_call_itself`.
- F8: compute the name check lazily.
- Tests: `task test:one` on `decreasing-match-fact`,
  `decreasing-plain-if`, `decreasing`, `decreasing-match-unnamed`;
  `hash_stability` for the changed examples.

**Lane B (Sonnet, about 45 min, can run beside lane A if it touches only
examples and docs): stage 2 tests and docs.**
- F3: a nested `match`, a dropped `let` (`drain` with `let fewer`), a kept
  equation, two scrutinees, an under-a-lambda `match` with `f.unfold`'s
  form pinned, a lexicographic measure, a named-`match` reject (no arm
  note), and a guard-call reject (pairs with lane A's F4; land after it).
- F9 and F5: the comment and doc fixes, and the `syntax.md` sentences.
- Tests: `task test:one` on the touched examples, `snap:hashes` and
  `hash_stability`, and the guide snippet check.
