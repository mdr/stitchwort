# Proposal: "enough fuel finishes" (SW-2137)

Design note only, 7 Nov 2026. Nothing here is built. It answers the open
item of gap 7 in `docs/reviews/aoc-gaps-status-2026-11-07.md:87`: "enough
fuel finishes" (2020 days 11 and 19, 2024 day 17) has no design. It builds
on the friction synthesis (`docs/research/aoc-friction-synthesis.md:265-279`,
`:458-460`, `:530-532`) and fits beside `decreasing-with-hypothesis.md`
(SW-2013; stages SW-2029 to SW-2032), without repeating it.

## 0. Summary

**What users get.** A day whose loop has no measure (seats that fill and
empty, a program that may never halt) writes it with fuel, as it must. Today
each such day then proves, by hand, the same three facts about its loop:
what it stops at is a real answer, it stops whenever the answer comes within
the fuel, and more fuel changes nothing. 2020 day 11 spends 58 lines on them
(`Settle.sw:13-70`), 2021 day 11 about 30 (`Cascade.sw:120-151`), 2024 day 17
ten (`Run.sw:51-60`), and 2024 day 17 never proves the second at all, which
is why its least-A theorem only covers runs within its own fuel. With a
small std kit, `Loop.run`, those facts are lemmas the day calls, and a day
that does have a measure (2021 day 11: each round that changes something
flashes another octopus) proves "the fuel is enough" by showing the measure
shrinks at one step, instead of counting steps.

**The premise needs splitting first.** The three days named for this item
have three different fuel problems, and one lemma doesn't fix all three:

| Day | Why fuel | What the fuel costs | Fixed by |
|---|---|---|---|
| 2020 day 11, `settle` | no measure exists (seats go both ways) | the generic loop lemmas, 58 lines | the kit (§3), stage 2 |
| 2020 day 11, `firstSeat` | a measure exists (distance to the edge), but needs a `match`'s fact | a spec bound "not proved" | `decreasing` after SW-2030 (§2, design C), optional |
| 2024 day 17, `Machine.run` | the program may loop | 10 lines, and a missing completeness half | the kit, stage 4 |
| 2020 day 19, the matcher | tree recursion; the fuel needed depends on the *match*, not the input | about 100 lines: a rank, and fuel arithmetic | **none of these** (§1.2) |

**Recommendation.** Design A: a std `Loop.run` (a loop of a step function
that continues or stops, with fuel), its lemmas, and
`Nat.iterateUntilStableWithin` on top of it (SW-1476's function). It removes
about 90 lines from three days for about 2¾ hours of Sonnet lanes, and gives
2024 day 17 the completeness half it lacks. Generating a "more fuel" lemma
per definition (design B) removes less, for Opus generator work. Moving to
`decreasing` (design C) removes fuel only where a measure exists, which is
one of the four fuels above. 2020 day 19 stays as it is (§1.2, D3081).

**D questions:** D3080, D3081 (§6). **Tickets:** four lanes (§7).

## 1. The three days, in the code

### 1.1 2020 day 11: two fuels

**`settle`** (`aoc/src/Aoc/Year2020/Day11/Day11.sw:118-127`) runs rounds
until one changes nothing, at most `roundLimit` (1000) of them, and returns
`None` if they run out. Nothing bounds the rounds in general, so the fuel is
honest, and the day states exactly what happens: `part1Exactly` and
`part2Exactly` are "the answer, exactly when the spec's rounds settle within
the limit" (`Proofs/Parts.sw:80-87`).

What that costs is three lemmas about *any* step function with `DecEq`,
nothing about seats (`aoc/NOTES-2020.md:2974-2984`):

- `settleSound` (`Proofs/Settle.sw:20-33`, 14 lines): what `settle` stops at
  is reached by rounds, within the fuel, and a round leaves it alone.
- `settleComplete` (`Settle.sw:54-70`, 17 lines): if the rounds reach such a
  layout within the fuel, `settle` stops there.
- `settledUnique` (`Settle.sw:42-50`, 9 lines), from std's
  `Nat.iterateFixedLater` (`crates/elab/src/std/Nat/IterateRepeat.sw:16-19`).

Each also threads an invariant, `keep`/`agree` (`Settle.sw:20-23`): the
program's round equals the spec's only on layouts with the start's floor
plan. With `SettlesWithin` and the docs, 58 lines; `settledExactly`
(`Parts.sw:63-78`, 16 lines) then glues them into the `↔`.

**`firstSeat`** (`Day11.sw:73-89`) walks a line of sight with `steps :=
height + width` as fuel. Here a measure *does* exist: the walk leaves the
grid within that many steps on a rectangle. The day leaves "that the spec's
line of sight is long enough" unproved (`aoc/NOTES-2020.md:2905-2910`); the
spec has the same bound (`Spec/Spec.sw:68-73`), so the proofs hold either
way. The fuel costs no proof lines today; it costs a caveat.

### 1.2 2020 day 19: the fuel is a bound on derivations

The matcher, `leftAfterWith` and `leftAfterAllWith`
(`aoc/src/Aoc/Year2020/Day19/Day19.sw:97-111`), is two functions defined
together; each rule inside a rule costs one fuel, and `[]` is "nothing
matched". The fuel can't be dropped: `8: 42 | 42 8` recurses before reading
anything (`aoc/NOTES-2020.md:5312-5315`).

Soundness holds for any fuel (`Proofs/Sound.sw`). The cost is completeness
with the program's fixed fuel, `rules.enough message` (`Day19.sw:155-156`):

- the program computes a rank and checks the rules are productive
  (`Day19.sw:118-153`, `productiveWith`, `chain`, `chainThrough`,
  `rankBound`, `rank`, `productive`: about 35 lines);
- the proof shows the rank is one (`Proofs/Proofs.sw:16-56`,
  `chainBounded`, `rankBelow`, `lookupMember`, `productiveRanked`: about
  40 lines);
- and threads the fuel through the induction on the `Matches` derivation
  (`Proofs/Complete.sw:40-77`, `Fuelled`, `scaleStep`, `fuelledSplit`,
  `fuelledInner`: 38 lines, plus the `Fuelled` arguments in `completeAll`,
  `Complete.sw:79-112`).

That is the day's "about 100 of 337 proof lines on fuel"
(`aoc/NOTES-2020.md:5323`). The fuel a match needs is `read.length * bound
+ rank` (`Complete.sw:43-46`): it depends on how much of the message the
rule *will* read, which is an index of the derivation, not something of the
function's input. A "more fuel, same answer" lemma would replace
`fuelledSplit`'s case split with "prove each part at its own fuel, then
lift", saving perhaps 15 lines [inferred: not tried], and leave the rank and
the bound, which are the real cost. Neither the kit nor `decreasing` removes
those: a measure of the input doesn't decrease at the first rule of a
longer alternative (same message, any rank), and the matcher is also a
mutual pair (SW-199's mutual groups) whose later calls run on what an
earlier call left (case 3 of `decreasing-with-hypothesis.md` §1.4). The fix
the day's notes name, an `Aoc.Common.Grammar` with soundness and
completeness proved once (`aoc/NOTES-2020.md:5324-5332`), is the honest one,
and it waits for a second grammar day.

### 1.3 2024 day 17: a machine that may not halt

`Machine.run` (`aoc/src/Aoc/Year2024/Day17/Day17.sw:140-148`) takes at most
`fuel` steps and ends `Finished output`, `Faulted` or `OutOfFuel`; the fuel
is `fuelFor`, `(A + 1) * (length + 1)` (`Day17.sw:150-155`). A program may
loop, so no measure exists in general.

- `runMoreFuel` (`Proofs/Run.sw:51-60`, 10 lines, and
  `outOfFuelNotFinished`, `Run.sw:21`) is "more fuel, same answer". Nothing
  in the day uses it yet (grep finds only its own recursion).
- Missing entirely: the other direction, "a halting run of the puzzle's
  computer (`Halts`, `Spec/Spec.sw:98-103`) finishes, given enough fuel".
  That is why `part2Least` is stated over `Debugger.outputFor`, runs with
  `fuelFor` steps, and not over every A the puzzle counts
  (`Proofs/Proofs.sw:19-21`, `aoc/NOTES-2024.md:5372-5377`, ranked item 4 at
  `:5559-5561`: "a std lemma that a fuelled run with at least as much fuel
  as a halts-in-n-steps derivation finishes, so per-program step bounds plug
  in").

Two halves, then. "Some fuel finishes" is a 15-line induction on `Halts`
once the run is a loop with a count (§3). "*This* fuel finishes" needs a
step bound for the particular program, which no generic lemma can give
(the halting problem is in the way); what the kit gives is a way to plug a
measure in (`Loop.runMeasure`), so a future per-program proof shows the
loop's state shrinks at each pass rather than counting steps.

### 1.4 The same shape elsewhere

- **2021 day 11** `cascade` (`aoc/src/Aoc/Year2021/Day11/Day11.sw:75-84`)
  is `settle`'s shape, with fuel `cells.length` and the result on running
  out instead of `None`. Its `Cascade.sw:77-151` proves the fuel is enough:
  a round that changes something flashes one more octopus
  (`stableOfCount`, `stableOrCount`, `stableAtSize`, `stableAbove`), then
  walks the fuel (`cascadeStep`, `cascadeAfter`, `flashersStable`, lines
  120-151). The measure part is the day's own; the walk, about 30 lines, is
  generic.
- **2024 day 6** `walk` already uses `Nat.iterateFixedLater` for "gone
  stays gone" (`Year2024/Day06/Proofs/Bound.sw:33-36`, 3 lines). It shows
  the pattern works: a loop whose finished state a step leaves alone gets
  "more fuel, same answer" for free.
- **2020 day 7** `bagsWithin` (`Year2020/Day07/Proofs/Part2.sw:49-67`,
  25 lines of "deeper keeps the answer") is tree recursion through
  `List.allSome`, like day 19, not a loop. Not covered.

### 1.5 What `decreasing` already does

A `decreasing` definition is compiled to fuel that carries its own proof of
being enough, and the compiler generates `f.%irrel`, "the amount of fuel
doesn't matter", and `f.unfold`, so a user never sees the fuel
(`crates/elab/src/decreasing.rs:1-34`, `decreasing_irrel` at `:1512`). So
"enough fuel finishes" is solved wherever `decreasing` applies; the item is
about the loops it can't apply to. std's own `Nat.divFuel`
(`crates/elab/src/std/core/Division.sw:9-38`) is SW-199's `Nat.div` item,
not this one.

## 2. Designs compared

**(A) A std loop kit.** One function and its lemmas, for loops written as a
step that either continues from a new state or stops with a result (§3).
A day writes its loop's step, not its recursion, and calls the lemmas. This
is the shape of every loop in §1.1, §1.3 and §1.4, and SW-1476's
`Nat.iterateUntilStableWithin` is one instance. The lemmas are proved once
from `Nat.iterate` and `Nat.iterateFixedLater`, which std has.

- Removes: `Settle.sw`'s three lemmas (2020 day 11, about 45 of its 58
  lines remain as calls of a line or two), `cascadeStep`/`cascadeAfter`/
  `flashersStable`'s walk (2021 day 11, about 25), `runMoreFuel` (2024 day
  17, 10). About 80-90 lines, medium confidence.
- Adds: 2024 day 17's missing completeness half (about 15 day lines), and a
  measure lemma that turns "the fuel is enough" into "this shrinks at a
  step".
- Costs: the days' loops are rewritten onto `Loop.run` (a few lines each:
  the step becomes a function returning `Continue`/`Stop`). Sonnet work.
- Rules out: nothing; it's a library.

**(B) Generate `f.moreFuel` for each fuelled definition**, as `f.unfold`
is generated now. The compiler would spot a definition structural on a
`Nat` whose `Zero` case is a constant (`None`, `[]`, `OutOfFuel`), and
generate "if it gave an answer that isn't the constant, more fuel gives the
same". The lemma is only true when the body uses each recursive result
"strictly" (`flatMap`, a `match` whose arm for the constant gives the
constant). 2024 day 17's `run` passes; 2020 day 7's `allSome` and 2020 day
19's `[]`-as-nothing (whose order is "more leftovers", not "the same
answer") don't, or need a different statement. So the generator needs a
strictness check, a note when it fails, and a second statement form, for
about 10 lines on one day plus whatever new days bring. Lean 4's
`partial_fixpoint` is this design done properly (a monotonicity proof
obligation over a chosen order, discharged by a `monotonicity` tactic, and a
fixpoint induction principle), as is Isabelle's `partial_function` for the
option monad; both are a large piece of machinery [from memory, not
checked]. It also hides the generic facts (soundness, completeness) that
the days actually spend lines on: B gives the 10-line half, not the
45-line one. Rejected for now.

**(C) Move the days to `decreasing` once SW-2029 and SW-2030 land.** That
removes fuel entirely, but only where a measure exists:

- 2020 day 11 `firstSeat`: yes. With SW-2030, `match from.offset (…) with
  | Some next =>` gives the arm its fact, and a grid lemma turns it into
  `distance < height + width`, so `decreasing height + width - distance`
  works and `steps` goes; the spec's `lineOfSight` could then drop its
  bound too, which retires the "not proved" item. Medium-low confidence:
  the grid lemma is new, and the spec side changes as well. Worth doing
  only when a lane is in day 11 anyway (§7, stage 3).
- 2020 day 11 `settle`, 2024 day 17 `run`: no measure. Never.
- 2021 day 11 `cascade`: a measure exists (octopuses not yet flashed), but
  it needs an invariant (flashers grow and stay on the grid) carried as a
  parameter, as `Nat.iterateUntilStable` does with `shrinks`
  (`crates/elab/src/std/Nat/Iterate.sw:41-47`). Possible today; the kit's measure lemma
  does the same with less change to the program.
- 2020 day 19: no (§1.2).

**Which removes the most code, for the cost.**

| Design | Lines removed (three days + 2021 day 11) | New capability | Cost |
|---|---|---|---|
| A, the kit | about 80-90 | 2024 day 17 completeness; measure lemma | ~2¾ h Sonnet (4 lanes) |
| B, generated | about 10 | none | ~3 h Opus generator |
| C, `decreasing` | `firstSeat`'s fuel only | day 11's spec bound proved | 45 min Sonnet, after SW-2030 |

A, with C for `firstSeat` folded into A's day 11 lane once SW-2030 has
landed.

## 3. The statement

In a new std file, `crates/elab/src/std/Nat/Loop.sw` (beside `Iterate.sw` and
`IterateRepeat.sw`; not std core, so no native pins move). Names are my
call (§6).

```
--| What one step of a loop does: go on from a new state, or stop with
--| a result.
type LoopStep s r =
  | Continue (next: s)
  | Stop (result: r)

--| Apply `step` from `start` until it stops, at most `fuel` times: the
--| result it stopped with, or `None` if the fuel ran out first.
def Loop.run (step: s → LoopStep s r) (start: s): (fuel: Nat) → Option r
  | Zero => None
  | Succ more =>
    match step start with
      | Continue next => Loop.run step next more
      | Stop result => Some result

--| Where the loop is after `count` steps: still going from a state, or
--| stopped with a result (which later steps leave alone).
def Loop.after (step: s → LoopStep s r) (count: Nat) (start: s): LoopStep s r :=
  Nat.iterate count (match | Continue state => step state | Stop result => Stop result) (Continue start)
```

The lemmas, in the order they are proved:

```
--| A run gives a result exactly when the loop has stopped with it by then.
theorem Loop.runAfter (step: s → LoopStep s r) (start: s) (fuel: Nat) (result: r):
    Loop.run step start fuel = Some result ↔ Loop.after step fuel start = Stop result

--| More fuel, same answer.
theorem Loop.runMore (step: s → LoopStep s r) (start: s) (fuel: Nat) (more: Nat) (result: r)
    (finished: Loop.run step start fuel = Some result) (enough: fuel ≤ more):
    Loop.run step start more = Some result

--| Two runs that finish agree, whatever their fuel.
theorem Loop.runAgree (step: s → LoopStep s r) (start: s) (first: Nat) (second: Nat) (one: r) (other: r)
    (finishedOne: Loop.run step start first = Some one) (finishedOther: Loop.run step start second = Some other):
    one = other

--| Enough fuel finishes, counted: a loop that has stopped within
--| `count` steps gives that result with any fuel from `count` on.
theorem Loop.runEnough (step: s → LoopStep s r) (start: s) (count: Nat) (result: r)
    (stopped: Loop.after step count start = Stop result) (fuel: Nat) (enough: count ≤ fuel):
    Loop.run step start fuel = Some result

--| Enough fuel finishes, by a measure: if every step that goes on keeps
--| `keep` and makes `measure` smaller, more fuel than the start's measure
--| finishes.
theorem Loop.runMeasure (step: s → LoopStep s r) (measure: s → Nat) (keep: s → Prop)
    (shrinks: (state: s) → keep state → (next: s) → step state = Continue next → keep next ∧ measure next < measure state)
    (start: s) (kept: keep start) (fuel: Nat) (enough: measure start < fuel):
    ∃ (result: r) => Loop.run step start fuel = Some result
```

`runMeasure` with `runAgree` is the sentence in the ticket: given more fuel
than the measure needs, the run finishes, and with the same answer as any
other run that finishes. `runEnough` is the counted form for a spec that
counts steps itself (2020 day 11's `Nat.iterate reached specRound start`),
and for a derivation such as 2024 day 17's `Halts`, where the day proves
`∃ count => Loop.after step count start = Stop …` by induction on the
derivation, one step per constructor, with no arithmetic.

Proofs: `runAfter` by induction on `fuel`; `runMore` from `runAfter` and
`Nat.iterateFixedLater` (`Stop` is left alone); `runAgree` from `runMore`
at the larger fuel; `runEnough` from `runAfter` and `runMore`;
`runMeasure` by induction on `fuel`. About 60 lines with docs, examples and
`test`s.

One more lemma the days need, for the invariant 2020 day 11 threads
(`agree` only on kept layouts):

```
--| Two steps that agree on the states `keep` holds of, from a start it
--| holds of, iterate the same, when `keep` is kept.
theorem Nat.iterateCongOn (f: a → a) (g: a → a) (keep: a → Prop)
    (keeps: (x: a) → keep x → keep (f x)) (same: (x: a) → keep x → f x = g x):
    (count: Nat) → (x: a) → keep x → Nat.iterate count f x = Nat.iterate count g x
```

And SW-1476's function, on the kit:

```
--| Apply `step` until it changes nothing, at most `fuel` times: the value
--| it leaves alone, or `None` if the fuel ran out first. Use it when
--| nothing shrinks at each step; with a measure, use `Nat.iterateUntilStable`.
def Nat.iterateUntilStableWithin [auto eq: DecEq a] (step: a → a) (start: a) (fuel: Nat): Option a :=
  Loop.run (x => if step x == x then Stop x else Continue (step x)) start fuel

theorem Nat.iterateUntilStableWithinSound [auto eq: DecEq a] (step: a → a) (start: a) (fuel: Nat) (final: a)
    (found: Nat.iterateUntilStableWithin step start fuel = Some final):
    ∃ (count: Nat) => count < fuel ∧ Nat.iterate count step start = final ∧ step final = final

theorem Nat.iterateUntilStableWithinComplete [auto eq: DecEq a] (step: a → a) (start: a) (final: a)
    (fixed: step final = final) (count: Nat) (reached: Nat.iterate count step start = final) (fuel: Nat) (within: count < fuel):
    Nat.iterateUntilStableWithin step start fuel = Some final

--| The steps settle on at most one value.
theorem Nat.iterateFixedUnique (step: a → a) (start: a) (one: a) (other: a)
    (first: ∃ (count: Nat) => Nat.iterate count step start = one ∧ step one = one)
    (second: ∃ (count: Nat) => Nat.iterate count step start = other ∧ step other = other):
    one = other
```

`Sound` and `Complete` are 2020 day 11's `settleSound` and `settleComplete`
without the seats (`Settle.sw:20-23`, `:54-58`), and `iterateFixedUnique`
is its `settledUnique`. Day 11 then states its `agree`/`keep` bridge once,
with `Nat.iterateCongOn`, instead of inside each lemma.

**What a user sees.** The guide's recursion chapter
(`docs/guide/07-recursion.md`, the "Note 2 … give it fuel" passage at
`:82`) gains a short section: when there is no measure, write the loop's
step and run it with `Loop.run`; the lemmas say what it found and that more
fuel changes nothing; with a measure that needs an invariant, `runMeasure`
says the fuel is enough. A checked example: a Collatz-style loop, whose
stopping is open, with `runMore` and `runAgree` used on it. The
`E-TERMINATION` note that mentions fuel could name `Loop.run` [my call;
stage 1 decides whether the note changes].

## 4. What the days look like afterwards

**2020 day 11.** `Layout.settle` goes; `settledOccupied` is
`Nat.iterateUntilStableWithin (.round plan) layout roundLimit |> .map
(.occupied)`. `Settle.sw` shrinks to the `SettlesWithin` definition and the
bridge: the program's round iterates as the spec's on kept layouts
(`Nat.iterateCongOn`), then `Sound`/`Complete`/`iterateFixedUnique`.
`part1Exactly`/`part2Exactly` keep their statements, which is the check
that nothing was lost. With SW-2030 landed, `firstSeat` loses `steps` too
(design C), if the grid lemma comes easily; if not, it stays.

**2024 day 17.** `Machine.run` becomes a step on a `Running` record
(`machine`, `printed`) that continues, stops with `Finished`, or stops with
`Faulted`, run with `Loop.run … |> .getOrElse OutOfFuel`. `runMoreFuel`
goes (`Loop.runMore`). New: `haltsStops`, `Halts program machine rest → ∃
count => Loop.after … count … = Stop (Finished (printed.reverse ++ rest))`,
by induction on `Halts`; with `Loop.runEnough`, any run with at least that
fuel finishes with the halting run's output. The "Not proved" line
(`Proofs.sw:19-21`) narrows to exactly the per-program step bound: "that a
halting run of a loop-shaped program finishes within `fuelFor` steps". A
`part2LeastWith` taking that bound as a hypothesis states the least-A
theorem over every A the puzzle counts.

**2021 day 11.** `cascade` becomes `iterateUntilStableWithin`, with the
result on running out (`getOrElse`). `cascadeStep`, `cascadeAfter` and
`flashersStable` go; `stableOfCount` (the step that changes something
flashes another octopus) becomes `runMeasure`'s `shrinks`, with measure
"octopuses on the grid not yet flashed" and `keep` "on the grid". Medium
confidence on the count: I read the statements, not every proof.

**2020 day 19.** Unchanged (§1.2, D3081).

## 5. Risks

- **The days' programs change.** Each loop is rewritten onto `Loop.run`.
  Run time should be the same (one call through a step function per round;
  the round dominates). Hashes and the days' answers tests catch any
  slip.
- **`Loop.after`'s clause lambda inside `Nat.iterate`** may print badly in
  goals (gap 4's readback). If it does, a named `Loop.advance step` for the
  lambda. Stage 1's call.
- **`if step x == x then Stop x else Continue (step x)`** computes `step x`
  twice unless the elaborator shares it (gap 9's compute-once). Written
  with a `let`; proofs then see the `let`, which 2020 day 11's `settle`
  already handles (`Day11.sw:126`).

## 6. Decisions for Matt

- **D3080:** Widen SW-1476 into a std loop kit: `Loop.run` (a step that
  continues or stops, run with fuel) with "more fuel, same answer" and
  "enough fuel finishes" (counted and by a measure), and
  `Nat.iterateUntilStableWithin` as its first use; rather than generating a
  "more fuel" lemma for every fuelled definition? [rec: yes. It removes
  about 90 lines from 2020 day 11, 2021 day 11 and 2024 day 17, gives 2024
  day 17 the completeness half it lacks, needs no compiler change, and is
  Sonnet work. Generating lemmas would remove about 10.]
- **D3081:** Leave 2020 day 19's fuel as it is until a second grammar day
  justifies an `Aoc.Common.Grammar` (or SW-199's mutual groups land),
  rather than designing a fuel lemma for tree-shaped recursion now? [rec:
  yes. Its 100 lines are a rank and a bound on derivations, which neither
  the kit nor `decreasing` removes; a "more fuel" lemma would save about
  15.]

Calls I made, and why:

- **Names:** `LoopStep` (`Continue`/`Stop`), `Loop.run`, `Loop.after`, the
  lemma names above. `Step` is taken by 2024 day 17, and `Done` by std's
  effects (`crates/elab/src/std/core/Effect.sw:13`).
- **`Option` result.** A day with a third outcome (2024 day 17's
  `OutOfFuel`) maps `None` to it; a day with a default on running out
  (2021 day 11) uses `getOrElse`. No class of "bottom" values.
- **Direct recursion for `Loop.run`, `Nat.iterate` for `Loop.after`.**
  The run reads like the days' own loops; the iterate gives the lemmas
  std's `iterateFixedLater` for free.
- **Design C only for `firstSeat`, inside the day 11 lane**, not as a lane
  of its own.
- **Not in the kit:** a lemma for tree recursion (2020 days 7 and 19).
  Two days with different orders ("the same answer", "more leftovers")
  aren't enough to choose one.

## 7. Tickets to file

In order; stages 2 to 4 each need stage 1, and stage 3 needs stage 2. The
day lanes touch different days, so 3 and 4 can run side by side.

1. **std: `Loop.run` and its lemmas** (`LoopStep`, `Loop.run`,
   `Loop.after`, `runAfter`, `runMore`, `runAgree`, `runEnough`,
   `runMeasure`; `Nat.iterateCongOn`), in `crates/elab/src/std/Nat/Loop.sw`, with full API
   docs, examples and `test`s. Also the guide section (§3) with its checked
   example. Sonnet. 60 min. Tests: `task test:one` on the new file's tests
   and the guide snippet; `snap:hashes` and `hash_stability` (new std
   definitions). Absorbs the "enough fuel finishes" half of SW-1476.
2. **std: `Nat.iterateUntilStableWithin` on `Loop.run`**, with `…Sound`,
   `…Complete` and `Nat.iterateFixedUnique`. Sonnet. 45 min. Tests: as
   stage 1. This is SW-1476's original function; SW-1476 closes with it.
3. **2020 day 11 and 2021 day 11 onto the kit.** `settle` and `cascade`
   become `iterateUntilStableWithin`; `Settle.sw` and `Cascade.sw`'s walk
   become calls (§4). If SW-2030 has landed, try `firstSeat` as
   `decreasing` (design C) and stop at 15 minutes if the grid lemma
   resists. Sonnet (AoC follow-up). 60 min. Tests: both days' `check` and
   `test` (targeted); `task audit:touched -- Aoc.Year2020.Day11` and
   `-- Aoc.Year2021.Day11`. The `part1Exactly`/`part2Exactly` and
   `flashersCorrect` statements must not change.
4. **2024 day 17 onto `Loop.run`, and completeness of runs.** `run` on the
   kit, `runMoreFuel` gone, `haltsStops` proved, `part2LeastWith` stated
   with the step bound as a hypothesis, and the "Not proved" line and the
   day's NOTES item 4 narrowed (§4). Sonnet. 50 min. Tests: day 17's
   `check` and `test` (targeted); `task audit:touched --
   Aoc.Year2024.Day17`.

Total about 3¾ h with stage 3's extras; 2¾ h for stages 1, 2 and 4.

Not filed: design B (generated lemmas); 2020 day 19 (D3081); 2020 day 7's
`bagsWithin` (tree recursion, same reason).

## What this note didn't cover

- Days in gap 7 whose cost is termination rather than fuel (2024 days 12
  and 16's measures, 2021 days 12 and 16): those are
  `decreasing-with-hypothesis.md`'s.
- Whether `omega` closes `runMeasure`'s `shrinks` obligations on 2021 day
  11 directly; stage 3 finds out.
- Run-time measurements of the rewritten loops (read-only lane).
- Every per-day line count is from reading the files cited, not from
  running anything; the "lines removed" figures are estimates.
