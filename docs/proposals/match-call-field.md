# Proposal: `match` and `rewrite` on a field of a call, `(f x).i`

**Status:** draft 1, 7 November 2026, for Matt's decisions D2990 to D2992 ([§7](#7-decisions)).
Ticket SW-1999, from SW-1913 (the six AoC proofs record eta broke). Written against `main` at
`4e5537f31`. Nothing was run for this note: it is read only (the shared machine was checking
proofs).

Related: [record-eta.md](record-eta.md) §6.4 (rule 2, and the principle that its fields are
projections of the scrutinee *as it was*); [the as-merged review](../reviews/record-eta-as-merged.md)
F1, F5 and F9; [goal-as-written.md](goal-as-written.md); [bounded-readback.md](bounded-readback.md)
§4.1 (D2542) and its stages 3, 6a and 6b (SW-1838, SW-1839, SW-1840);
[well-founded-recursion.md](well-founded-recursion.md), "As built" item 5 (a `decreasing`
definition is folded by name). Repros: `docs/repros/sw-1913/match-field.sw` and
`call-field-match3.sw`.

Labels: **[checked]** read in this repository at the place given; **[cited]** read in the note
named; **[inferred]** my reasoning from the code, not run, with a confidence where it matters.

## 0. Summary

**What users hit.** Since record eta, a proof that `match`es on something and then expects the
goal to have changed sometimes finds the goal unchanged, and a proof that expects it unchanged
finds it rewritten into a definition's internals. In 2021 day 15 a `match` on
`Nat.decEq cave.height 0` doesn't reach the copy of that test inside `cave.tiled.level`, so
the branch's `rfl` fails. In 2024 day 23 a `match` on the search's size test reaches *into*
`network.links.largestFrom …`, a `decreasing` definition, so the goal shows its fuelled
internals and the step lemmas that rewrite the call no longer find it. Both are workarounds
marked SW-1913 today.

**Why.** Neither is about `match`. Both are about the **value** record eta makes for a field
of a call, which every reader then sees:

1. **A function field of a stuck call, applied** (`cave.tiled.level position`) becomes a stuck
   term the evaluator doesn't recognise as a field of a call any more, so neither the unfolded
   read-back nor conversion looks inside it (§2.1).
2. **A field of a folded call** (a `decreasing` definition, `(largestFrom …).items`) is the
   projection of the call's *unfolding*: rule 2 keeps the call only for glued calls, and a
   folded definition isn't one (§2.2).

The missing `Proj` arm in `match`'s as-written check (review F5) is real but small: it makes
`match` throw away a correct as-written result, and it doesn't cause either failure on its own
(§2.4).

**The change, in one line each.**

- **Stage 1:** applying (or `J` on) a stuck field of a call computes it first, the way an
  over-applied call already does; and F5's `Proj` arm.
- **Stage 2:** rule 2 keeps a folded call in its fields as it keeps a glued one: `(f x).i`,
  not `(the inside of f x).i`. Elaborator only; the kernel is unchanged. (As built: gluing
  alone doesn't mean "elaborator only", since the kernel checks bodies and signatures glued;
  stage 2 is gated on `Machine::kernel` instead, §10.)
- **Stage 3:** remove the three SW-1913 workarounds in 2021 day 15 and 2024 day 23.

**The rule they give** (D2990): *a field of a call behaves like the call.* `(f x).i` is shown
as written; a `match` or `rewrite` on `f x` finds it there; and one on something inside `f`'s
body looks inside exactly when it would look inside `f x` standing alone. That's how goals
behaved before eta, and what the AoC proofs were written against.

None of this waits for 6a and 6b, and they don't fix it: they change how searches choose
among what they see; these stages fix what there is to see (§5).

## 1. Background: the forms a field of a call takes

Three representations matter. All are in `crates/core/src/value.rs` **[checked]**.

- **A glued call** `Value::Call(f, spine, cell)`: a definition applied to all its arguments,
  not yet unfolded, with a cell for its unfolding. Only with `glue` on (`quote_folded`'s doc,
  `value.rs:2316-2321`). That includes the kernel while it checks a definition's body or
  signature (`check.rs`, `admit_group` and `declare_def`), which this note first missed (§10).
- **A field of a glued call**, `Value::Call(f, [args…, .i], cell)` (`project_call`,
  `value.rs:1924-1934`). Rule 2 binds a branch's fields to these when the scrutinee was a
  glued call (`eta_fields`, `value.rs:1974-1990`), so that goals keep `(Set.map s f).items`
  rather than the inside of `Set.map`.
- **A stuck field of a call**, `Neutral(Def f, [args…, .i])`: what forcing the previous one
  gives when the call is stuck (`Frame::CallField`, `value.rs:1627-1657`), and what
  `eta_fields` presets the cell to (SW-1829's fix for exponential forcing). It is "a name for
  that projection": `is_folded` counts it as folded (`value.rs:2152-2161`), so conversion
  unfolds it before answering "different" (`value.rs:2973-2985`), and the unfolded read-back
  writes it as the field of the call's unfolding (`value.rs:2600-2616`).

`is_folded` recognises the stuck form only when **every** elimination after the arguments is
a projection (`value.rs:2158`), and `is_call_field` only when the **last** one is
(`value.rs:669-671`).

And one more kind of call: a **folded** definition, `Neutral(Def f, args)`, which stays as
written until something takes it apart. That's dictionaries, theorems, `decreasing`
definitions (`Def::fold`, `folds`, `value.rs:2091-2094`; well-founded-recursion.md "As built"
item 5 **[cited]**) and definitions with a `Quot.lift` leaf (`folds_on_lift`,
`value.rs:2206-2208`). A folded definition is never glued: `unfold_now` glues only when
`!folds(g, id)` (`value.rs:2061-2075`).

## 2. The three cases, traced

### 2.1 2021 day 15, `Levels.sw:82`: an applied function field hides the call

**What the user sees.** `tiledLevelsAgree` matches on `Nat.decEq cave.height 0`, then on the
width test, then on the position. In the last branch, `rewrite found, raised in rfl` fails:
the right side still holds `cave.tiled` stuck on the height test, as though the first `match`
never happened. The workaround is a new lemma, `tiledIsTiles` (`cave.tiled = cave.tiles` when
the cave has rows and columns), rewritten in by hand (`Levels.sw:91-93`). The repro is
`match-field.sw`: `cave.tiled.level n = (if cave.height != 0 then n + 1 else n)` by `match h:
Nat.decEq cave.height 0` and `rfl` in both arms.

**The trace.** `RiskMap.levelAt risks position` is `boxEnter risks.height risks.width
risks.level position`, which applies `risks.level` to `position` (`Day15.sw:51`,
`GridGraph.sw:41-42`) **[checked]**. With `risks` the glued call `Cave.tiled cave`:

1. `risks.level` is the accessor `RiskMap.level`, whose `case` forces `Cave.tiled cave`. It is
   stuck on the height test, so rule 2 fires and `eta_fields` returns the field of the call,
   `Call(Cave.tiled, [cave, .level])`, its cell preset to the stuck form
   `Neutral(Def Cave.tiled, [cave, .level])` (`value.rs:1978-1989`).
2. Applying that to `position`: a call applied is forced first (`apply_later`, `apply_call`,
   `value.rs:957-968`), which gives the stuck form, and then `apply_step` meets a
   `Neutral(Head::Def(id), spine)`, pushes the argument and asks to unfold `Cave.tiled` with
   the spine `[cave, .level, position]` (`value.rs:937-941`).
3. `unfold_now` finds a spine longer than the arity and returns it as it is
   (`value.rs:2060-2081`). The result, `Neutral(Def Cave.tiled, [cave, .level, position])`,
   ends in an application, so `is_call_field` is false; and `folded_call` is false too
   (spine length isn't the arity). **It is no longer a name for anything: it's a rigid stuck
   term headed by `Cave.tiled`.**

Every reader then treats it as rigid:

- **The unfolded read-back**, which `match`'s usual occurrence test reads (`matching.rs:927-936`),
  skips the stuck-field case (`value.rs:2602-2604`) and writes the term
  `(Cave.tiled cave).level position` with `Cave.tiled cave` as a plain application: the height
  test inside `Cave.tiled` isn't in the term, so the `match` can't replace it.
- **Conversion** doesn't unfold it either (`is_folded` false at `value.rs:2973`). So it is
  "different" from the same field reached another way, such as `(the unfolding of Cave.tiled
  cave).level position`. That's a completeness gap, not a soundness one: it can only make
  something true fail to check **[inferred, high]**.

Before eta, the accessor's `case` was stuck on the glued call, so the value was
`Neutral(Def RiskMap.level, [Call(Cave.tiled, [cave]), position])`: the call sat in an
*argument*, which the unfolded read-back unfolds, so the height test was visible and replaced.
**[inferred, high: each step checked, the composition not run]**

The fields `.height` and `.width` aren't applied, so they keep the stuck form and read back as
the field of the unfolding: that's why `tiledSize`'s `match`es still work (`Answers.sw:20-28`),
and only the applied `.level` fails.

### 2.2 2024 day 23, `Part2.sw:179`: a folded call's field shows its internals

**What the user sees.** `largestFromAnswers` recursed with `decreasing candidates.size`, and in
each branch rewrote `network.links.largestFrom clique candidates best` with a step lemma
(`largestPruned`, `largestDone`, `largestStep`). After eta, `match fits: Nat.leq (clique.size
+ candidates.size) best.size` rewrites *inside* the call, the arms' goals show its fuelled
internals, and the step lemmas find no call to rewrite. The workaround names the answer
`result`, with an equation `same`, so that the goal never holds the call
(`Part2.sw:166-224`). The repro is `call-field-match3.sw`: `match same: pick n empty` on
`Fits (pick n empty)` finds nothing (`probeCall`), and `match small: Nat.leq n 1` rewrites
inside `pick` (`probeTest`).

**The trace.** `Set` is a record, `{ items: Map k () }` (`std/Set/Set.sw:12`), and
`Bag` in the repro is `{ items: List Nat }`; both have eta. `pick n empty` is a `decreasing`
definition, so it is folded: `Neutral(Def pick, [n, empty])`, not a glued call.

1. `Bag.items (pick n empty)` runs the accessor's `case`. Its scrutinee is a folded call, so
   the machine unfolds it (`Frame::Scrutinee`, `folded_call`, `unfold_for`,
   `value.rs:1679-1681`, `2126-2140`): `pick`'s fuelled helper, stuck on `Nat.leq n 1`.
2. Rule 2 fires and calls `eta_fields` with the *unforced* scrutinee, which is the folded
   `pick n empty`. `eta_fields` keeps the call only for a `Value::Call` (`value.rs:1975-1977`);
   anything else gets `project(d, i, forced)`, the field of the **unfolding**.
3. So `(pick n empty).items` is `(the fuelled helper, stuck).items`, and the call is gone from
   the value itself, not just from one read-back of it.

From there:

- **`probeCall`:** the usual test reads the goal back unfolded and looks for `pick n empty`
  (a folded call reads back as itself). It isn't there. The as-written stage does see it, in
  the goal as bound (`Fits (pick n empty)`, a glued call read back folded), but check 2
  compares the as-written result, unfolded, with the usual one: `Proj(items, x)` against
  `Proj(items, the helper …)`. `Finder::agree` has no `Proj` arm (`as_written.rs:731-765`),
  so it answers "disagree", and the as-written result is dropped (F5).
- **`probeTest`:** `Nat.leq n 1` isn't in the goal as written, but it is in the unfolded goal,
  inside the helper's `if`. The usual test replaces it, and the arms show the helper.

Before eta, the accessor's `case` was stuck, so the value stayed `Bag.items (pick n empty)`.
The unfolded read-back never opens a folded call, so neither test saw inside `pick`:
`probeTest`'s `match` refined nothing and the goal kept the call, which is what day 23's step
lemmas needed. **[inferred, high]**

The same holds for the other folded class with records: a definition with a `Quot.lift` leaf
that returns a record (a `Map.foldLeft` into one, as in SW-1829's `blinkCounts`). Its fields
are projections of the lift it unfolds to, where map-equality.md §7.2 meant the goal to show
the call. **[inferred, medium: no AoC failure found that rests on it]**

### 2.3 2021 day 15, `Answers.sw:34`: `let (Both …)` fails the motive check

**What the user sees.** `let (Both height width) := tiledSize cave rectangle` in
`part2Correct` gives a motive error; `.left` and `.right` work.

**What I can say without running it.** In a proof, a pattern `let` on an `And` stays a
generalised `match` (`patlet.rs:23-26`) **[checked]**, so its motive is built from the goal and
the variables' types read back unfolded. One of those is `same: tiledLevelAt cave =
cave.tiled.levelAt` (line 33), whose right side holds exactly §2.1's applied field. The likely
mechanism is that the motive check (`motive_checks_now` on the as-written path, `check_motive` on the usual one, `matching.rs:1047`, `1062`) compares two
spellings of that field: the rigid `(Cave.tiled cave).level p` from the read-back, and the
field of the unfolding applied to `p` from the bound value. §2.1's completeness gap makes them
"different". **[inferred, low to medium: the mechanism fits, but I couldn't tell which two
terms meet without running it.]** Stage 1 tests it directly: if the pattern `let` checks once
applied fields compute, it was this; if not, the stage reports the motive error and it gets its
own ticket.

### 2.4 F5 on its own

`Finder::agree` (`as_written.rs:731-765`) has an arm for every term form but `Proj`. Wherever a
target holds a projection that the as-written and usual results reach by different routes,
the as-written result is dropped. With stage 2, `probeCall` no longer needs it: the usual test
finds `pick n empty` inside `Proj(items, pick n empty)` by itself. It is still a real gap for
a scrutinee written differently under a projection (`match found: (xs.map (f a)).maximum`
against a goal holding `(xs.map (y => f a y)).…` under a field). It's five lines and a test
(review F5), and 6b deletes `agree` along with check 2 (D2542). Worth doing now, since 6b is
several lanes away, and its test survives as a behaviour test.

## 3. What the goal should show, and what `match` should find

The rule (D2990): **a field of a call behaves like the call.**

| | Glued call `f x` (ordinary definition) | Folded call `f x` (`decreasing`, `Quot.lift` leaf) |
|---|---|---|
| The goal shows | `(f x).i`, and `(f x).i a` when applied (but see D2992) | `(f x).i` |
| `match`/`rewrite` on `f x` | found in `(f x).i` | found in `(f x).i` |
| `match` on something inside `f`'s body | today: found inside (the usual test reads calls unfolded), as for `f x` alone; under D2542 (6b), only if nothing is visible, opening `f x` | not found, as for `f x` alone: a folded call is opened only by taking it apart, and a field read in a goal doesn't count |
| `rfl`, conversion | equal to the field of the unfolding | the same |

So 2021 day 15's `match` on the height test refines `cave.tiled.level position` as it
refines `cave.tiled.height`; and 2024 day 23's `match` on the size test leaves
`largestFrom …` alone, as before eta, so the step lemmas can rewrite it.

**Why this rule and not "projections are transparent".** One could argue a `match` should see
inside a `decreasing` call when a field of it is read, since rule 2 opened it anyway. But
that's an accident of when rule 2 runs (a `case` on an eta type takes its branch without
looking at the call), not something the user wrote. It also contradicts record-eta.md §6.4,
which already chose "projections of `x` as it was" for glued calls after two AoC proofs broke
the other way. This proposal extends §6.4 to folded calls, which it didn't cover.

**Prior art.** Lean 4 elaborates a `decreasing_by` definition as irreducible, so `(f x).1`
stays as written under `whnfR`, and `rw` and `match h :` abstract only visible instances
(`kabstract`): the call is visible and its inside isn't. Agda represents a field of a stuck
call as `Def f [Apply x, Proj i, Apply a]`, one head with a spine of applications and
projections in any order, which is option 1b below. **[from memory, not checked for this
note]**

## 4. Designs

### 4.1 Case 1, the applied field

**1a. Applying (or `J` on) a stuck field of a call computes it first** (recommended). In
`apply_step`'s `Neutral(Head::Def(id), spine)` arm, a spine that `is_call_field` (the last
elimination a projection) is a name for a projection, not a call short of arguments: unfold
it to the field of the call's unfolding (as `unfold_folded` does, but in the machine), then
apply. The same in `Frame::JForced` (today it unfolds `folded_call`s only, `value.rs:1566`) and
in `Replay`'s application step. The check is on the last elimination, so the hot path gains a
pattern test and nothing else (`apply_step` has no `g`, so it hands back a control state
that does the unfolding, on a cold path, as `apply_later` does for calls).

- *What it shows.* `cave.tiled.level position`, once forced, is `(the unfolding of
  cave.tiled).level position`, as any call applied beyond its arity already is (a glued call
  applied is forced, `apply_call`). The goal *as bound* still shows the call, since that's a
  glued call of `RiskMap.levelAt`.
- *Cost.* One re-run of the call per application of a stuck field. That's SW-1914's cost
  shape (F1), one more instance; SW-1914 gives the call's cell to the stuck form and removes
  it.
- *What it fixes.* §2.1, and §2.3 if the mechanism there is right. Conversion: the rigid
  term is gone, so the gap closes.

**1b. Allow eliminations after the projection in the stuck form.** `is_call_field`,
`is_folded`, `folded_parts`, `unfold_folded`, the read-back and the ten guarded sites F9
lists all accept `[args…, .i, more…]`: a call, then a field, then anything. This is Agda's
shape, and it keeps `(Cave.tiled cave).level position` folded in goals.

- *Cost.* Every site that reads the stuck form changes, and they are exactly the sites F9
  says are fragile (an `unreachable!` where a guard is missed). With SW-1914 option (b),
  which makes the stuck form a `Value::Call` with a filled cell, this becomes "a call's spine
  is its arguments, then any eliminations", one representation: the right end state if
  SW-1914 goes that way, but too much to take on for this fix.

**1c. Don't name function fields.** `Frame::CallField` and `eta_fields` would keep the stuck
form only for fields that aren't functions. Narrower than 1a, and wrong for the same reason
1a is right: the field can be passed as an argument (`boxEnter … risks.level position`) and
applied inside, where the type at the application site is all that's known.

**Recommendation: 1a now** (D2992). It's local, glued evaluation only (stuck fields of calls
exist only with gluing on; the kernel glues too, and §10 says why that's sound), and it gives over-applied fields the rule over-applied calls already
follow. 1b stays the end state to consider in SW-1914.

### 4.2 Case 2, the folded call's field

**2a. Rule 2 keeps a folded call in its fields** (recommended). In `eta_fields`, when the
unforced scrutinee is a folded call (`folded_call`: `Neutral(Def f, args)` with `folds` or
`folds_on_lift`) and the forced value is a stuck neutral (not an unknown), each field is the
stuck form `Neutral(Def f, [args…, .i])`. This shape is already there for glued calls, with all
its readers (§1): `is_folded` recognises it (a body, arguments, then projections), conversion
unfolds it through `unfold_folded`, which handles fields (`value.rs:2264-2271`), and the
unfolded read-back writes it as `Proj(i, f x)`, with `f x` read back as itself, since a folded
call forced stays folded (`force_call` → `unfold_now` → `folds`). Only in the elaborator: the
kernel keeps projecting the unfolding, which it never shows anyone. (As built, that's
`Machine::kernel`, not gluing, which the kernel turns on too; §10.)

- *Why the forced value must be a stuck neutral.* Then every field is stuck either way (the
  projection of a neutral), so naming it by the call changes no computation, only its name.
  If the forced value is an unknown, the fields stay projections of it, so the unifier can
  solve it (as `eta_fields`' `named` condition does today).
- *Cost.* A stuck field of a folded call has no cell, so conversion that meets it against
  something else unfolds the call again (F1's shape again). The read-back costs nothing extra:
  the call reads back as itself. Stage 2 measures day 23 and the `decreasing` days.
- *Soundness.* The kernel is unchanged (gated on `Machine::kernel`, §10). In the elaborator the stuck form is another name for
  the same projection, already relied on for glued calls; terms it reads back to are
  `Proj(D, i, f x)`, which the kernel checks itself.
- *What it fixes.* §2.2: both probes, and day 23's original proof. Display: goals show
  `(largestFrom …).items.size` again, not the helper.

**2b. Teach the searches to read `Proj(i, the unfolding of f x)` as `(f x).i`.** The value
keeps the unfolding and the read-back would have to rediscover the call, which it can't: the
call isn't in the value. Ruled out.

**2c. Wait for 6b.** Under D2542 the as-written stage would keep `probeCall`'s result with no
check 2. But `probeTest` finds nothing visible, so 6b looks inside, and the inside is in the
value itself: the goal would still show the helper. 6b doesn't fix day 23 (§5).

**Recommendation: 2a** (D2991). It's §6.4's own principle, applied to the folded calls §6.4
didn't mention.

### 4.3 The as-written check (F5) and `rewrite`

Add the `(Proj, Proj)` arm (review F5's text) in stage 1. Neither failure needs it once stages
1 and 2 are in, but it's a correct result thrown away, and cheap.

`rewrite` needs nothing for these cases: its as-written search reads the goal folded, where
`(f x).i` holds `f x` with its own key, and its fallback reads the unfolded goal, which after
stage 2 holds the folded call. One small improvement is not needed for correctness: a rule
whose left side is itself a projection (`h: (f x).i = v`) is keyed `Other("projection")`
(`rewrite.rs:1551`), so every projection in the goal is a candidate, tested by conversion.
A `Key::Proj(d, i)` would make it selective (record-eta.md §6.4's table names it). I'd file it
as a backlog ticket, not a stage here.

## 5. How this fits 6a and 6b, and whether to wait

**It shouldn't wait.** Stages 3, 6a and 6b (SW-1838 to SW-1840) change how searches choose:
the as-written occurrence whenever there is one, otherwise the reader's `find` inside the
calls whose arguments could hold the needle (D2542, D2538). These stages change **what the
value is**, which every reader sees: today's `quote`, the reader's `find` and `mentions`, and
conversion. Without them:

- 6b's `find` would meet §2.1's rigid neutral and not know to open it (it isn't a call or a
  stuck field), so day 15 would stay broken under 6b too; and conversion would still be
  incomplete there whatever the searches do.
- 6b would find day 23's internals in the value itself, as §4.2 (2c) says.

So stages 1 and 2 are prerequisites for 6b doing the right thing on fields, not alternatives
to it. In the other direction, nothing in them is undone by 6a or 6b: F5's arm goes when 6b
deletes `agree`, which is the only throwaway (five lines).

**What 6b's reader must do, as a requirement for SW-1838.** `find` and `mentions` treat a
stuck field of a call `(f x).i` as the call `f x` for the skipping rule (its arguments are
`x`), and open it as `unfold_folded` does. A folded call is opened only when `find` would open
any folded call; bounded-readback.md §4.2 doesn't say, and by §3's rule it shouldn't be,
since `quote` doesn't open one. I'd add these two lines to SW-1838's ticket rather than a
stage (an orchestrator board edit).

**Interaction with SW-1998** (doing, unifier eta gaps): it changes `same_field_records` for
`(f x).i` in `unify.rs`; these stages change `value.rs`. Different files, overlapping idea. The
stage briefs should say "after SW-1998 merges" only if its diff touches `eta_fields` or
`Frame::CallField`.

## 6. Stages

Sequencing is mine to decide, so these are decided, not questions: stages 1 and 2 run one after
the other (both in `value.rs`), 1 first because it also closes a conversion gap; stage 3 after
both.

### Stage 1: applied stuck fields compute; F5's arm

- **Change.** §4.1's 1a in `apply_step`, `Frame::JForced` and `Replay` (and the reference
  evaluator if it makes stuck fields of calls; the lane checks `reference.rs:350-395`);
  §4.3's `(Proj, Proj)` arm in `Finder::agree`.
- **Tests added.** `match-field.sw` as an accept example (both arms `rfl`); a conversion
  example, a field of a stuck call applied against the same field of its unfolding by `rfl`;
  an as-written example with a scrutinee written differently under a projection
  (`STITCHWORT_MATCH_METRICS` shows it kept).
- **Check in place.** With the stage applied, put back `rewrite found, raised in rfl` in
  `Levels.sw` and the pattern `let` in `Answers.sw` in the worktree, and run
  `task audit:touched -- Aoc.Year2021.Day15`. If the pattern `let` still fails, report its
  motive error (§2.3) and leave that workaround. The real removal is stage 3's.
- **Targeted tests.** `task test:one --` the new examples, `as-written`, and the record-eta
  examples; `task snap:hashes` and the `hash_stability` test for the new examples; the core
  unit tests for `value.rs`'s eta (`cargo test -p stitchwort-core eta`, about a minute).
- **Model, estimate.** Opus (core evaluator, D2506), 75 min.

### Stage 2: rule 2 keeps folded calls

- **Change.** §4.2's 2a in `eta_fields`, gluing on only.
- **Tests added.** `call-field-match3.sw` as an accept example: `probeCall`'s `match` finds
  the call, and after `probeTest`'s `match` each arm's goal still shows `pick n empty` (an
  `example` that rewrites by `pick`'s unfold lemma in an arm shows it). A display test:
  a hole's goal after `.items` of a `decreasing` call shows the call.
- **Check in place.** Put back day 23's original recursive `largestFromAnswers` in the
  worktree and run `task audit:touched -- Aoc.Year2024.Day23`. Time it against `main` (one run
  each, before and after).
- **Other days.** Proofs written since eta (7 Nov) may rely on seeing inside a folded call's
  field. The lane greps `aoc/` for `decreasing` definitions that return a record and runs
  `audit:touched` on those namespaces only, listing them in its report; a whole-AoC run needs
  Matt's OK first.
- **Targeted tests.** As stage 1, plus `cargo test -p stitchwort-elab decreasing` (or the
  `decreasing*.sw` examples by `test:one`).
- **Model, estimate.** Opus, 75 min.

### Stage 3: remove the SW-1913 workarounds in 2021 day 15 and 2024 day 23

- **Change.** `Levels.sw:91-93`: back to `rewrite found, raised in rfl`; drop `tiledIsTiles`
  if nothing else uses it. `Answers.sw:34-37`: back to `let (Both height width) := …` (if
  stage 1 found it fixed). `Part2.sw:166-231`: back to the recursive `largestFromAnswers`
  with the step lemmas rewriting the call; `largestFromAnswersAt` goes.
- **Targeted tests.** `task audit:touched -- Aoc.Year2021.Day15` and `-- Aoc.Year2024.Day23`;
  `stitchwort fmt` on the files.
- **Model, estimate.** Sonnet, 30 min. The other three SW-1913 workarounds belong to
  SW-1998 (2020 day 20, 2021 day 11) and SW-2000 (2021 day 2).

## 7. Decisions

- **D2990: the rule: a field of a call behaves like the call** in goals and in `match` and
  `rewrite`: shown as `(f x).i`, found by a search for `f x`, and looked inside exactly when
  `f x` alone would be (§3)? **[rec: yes, because it's how goals behaved before eta, what
  record-eta.md §6.4 chose for glued calls, and what the broken proofs were written against]**
- **D2991: a folded call keeps its fields as `(f x).i`** (`decreasing` definitions and those
  with a `Quot.lift` leaf), in the elaborator only, so a `match` never opens a `decreasing`
  call because a field of it was read (§4.2, 2a)? **[rec: yes, because otherwise goals show
  fuelled internals the user never wrote, and the kernel needs no change]**
- **D2992: a function field of a stuck call, once applied, shows as the field of the call's
  unfolding** (`(the inside of cave.tiled).level position`), as any call applied beyond its
  arity already does, rather than a new form that keeps `(cave.tiled).level position` (§4.1,
  1a over 1b)? **[rec: yes for now, because 1b changes every reader F9 calls fragile; revisit
  it with SW-1914, where one representation for calls and their fields would make 1b cheap]**

## 8. Tickets to file

| Order | Ticket | Model | Estimate | Tests | Replaces or absorbs |
|---|---|---|---|---|---|
| 1 | Stage 1: applied or `J`-eliminated stuck fields of calls compute first; F5's `(Proj, Proj)` arm in `as_written::agree` | Opus | 75 | new examples, `as-written`, record-eta examples, `snap:hashes`, `hash_stability`, core eta unit tests, `audit:touched -- Aoc.Year2021.Day15` | absorbs review F5 (noted on SW-1999); SW-1999 itself |
| 2 | Stage 2: rule 2 keeps folded calls in its fields (gluing on only) | Opus | 75 | as stage 1, `decreasing` examples, `audit:touched -- Aoc.Year2024.Day23` and the `decreasing`-record namespaces | — |
| 3 | Stage 3: remove the SW-1913 workarounds in 2021 day 15 and 2024 day 23 | Sonnet | 30 | `audit:touched` on the two days | the "then drop the workarounds" part of SW-1999 |
| — | Backlog: `rewrite` keys a projection by its field, `Key::Proj(d, i)` | Sonnet | 30 | `test:one -- rewrite` examples | record-eta.md §6.4's table item |
| — | Board edit, no lane: SW-1838 (`find`) gets §5's two requirements | orchestrator | — | — | — |
| — | Note on SW-1914: option (b) would make §4.1's 1b one representation (D2992's revisit) | orchestrator | — | — | — |

## 9. What this note didn't do

- **§2.3's cause isn't confirmed.** Stage 1's check in place confirms or rules it out.
- **No measurement.** Stage 2's cost (an extra unfolding when conversion meets a stuck field of
  a folded call) is argued, not measured; the stage times day 23.
- **The reference evaluator** (`crates/core/src/reference.rs`) wasn't read in full; whether it
  makes stuck fields of calls (and so needs stage 1's change mirrored) is left to the lane.
- **`cases`** (SW-2000's area) wasn't traced: its fallback reads stuck terms through
  `is_folded` (`cases.rs:1287`, `1348`), so stages 1 and 2 should help it, not hurt it, but
  that's unchecked.

## 10. As built (stages 1 and 2)

- **The kernel glues.** `in_kernel_modes` turns gluing off, but the kernel turns it on to check
  every body (`admit_group`) and signature (`declare_def`), so glued calls and stuck fields of
  calls exist in the kernel too. Stage 1's applied fields (`apply_field`, `Frame::FieldOf`)
  therefore run in the kernel. That's sound (review SW-2108 F1): the path unfolds only a body
  `body_seen` allows, runs in the same machine and budget, and takes and applies the field by
  the ordinary rules, which is what unglued evaluation computes already.
- **A `Quot.lift` leaf is computed through when a stuck field is applied** (SW-2108 F3 kept as
  it was). The review proposed leaving the call folded there, on the premise that unglued
  evaluation does. It doesn't: unglued, `f x` stays folded, but taking a field of it unfolds it
  through the lift (`Frame::ProjForced`, `unfold_for`), and the reference does the same. Left
  folded, glued `(f x).i a` is a rigid term no conversion opens, unequal to the unglued value
  (`call_fields::a_lift_leaf_calls_applied_field_is_the_same_glued_and_unglued` fails that
  way), which D3030 rules out. Showing `(f x).i a` folded needs §4.1's 1b.
- **A call with a `Quot.lift` leaf is glued** (`folds` covers dictionaries, theorems and
  `decreasing` definitions only), so its fields already took rule 2's glued branch; stage 2
  matters for it only in values made unglued.
- **Stage 2 is elaborator-only by a flag.** `Machine::kernel`, set by `in_kernel_modes`, says
  the kernel is checking; folded calls keep their fields as `(f x).i` only when gluing is on and
  it isn't (`names_folded_fields`). The kernel's values are as before. Two sites name them:
  rule 2 (`eta_fields`), and a projection `Term::Proj` of a folded call (`Frame::FoldedField`),
  which this note didn't trace (the goal `(pick n empty).items` is a projection, not an accessor
  call).

