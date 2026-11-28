# SW-5005: which AoC days genuinely benefit from streams

Stage S4 of std's infinite streams (docs/proposals/streams-head-tail.md, option
E), phase 1: a survey of `aoc/src` (2020, 2021, 2024, 2025) and
`games/rogue` for code that streams fit. Opus, 28 Nov 2026. Paper only: no
code was run, so every cost below is argued from the code, and is marked so.

Matt's question: "which AoC days might genuinely benefit from streams". The
bar: streams make the day clearer, shorter, easier to prove, or faster; not
merely that it could use them.

## Summary

Short answer: **two days benefit, modestly; most candidates are neutral;
four would get worse.** No day gets a proof it couldn't have before, and none
gets faster.

| Day | Shape now | With streams | Verdict |
|---|---|---|---|
| 2021 day 11 (octopus flashes) | two hand-written step loops (`flashesIn`, `firstSync` with fuel) and a third in the proofs (`stepsFrom`) | one stream of caverns; part 1 a sum over `take 100`, part 2 `findIndex` over `take syncLimit` | **genuine: clearer and shorter**; proofs likely shorter (std's `findIndex` lemmas replace two inductions), not certain |
| 2024 day 22 (monkey market) | `Nat.iterate 2000` for part 1, a hand-written `secrets` list for part 2, and the spec's own copy `secretNumbers` | one stream of a buyer's secrets: part 1 its `at 2000`, part 2 its `take 2001` | **genuine: clearer, a little shorter** (one sequence for both parts, as the puzzle tells it) |
| 2020 day 11 (seating) | `settle` with a round limit, until a round changes nothing | first adjacent repeat in `Stream.iterate round` | neutral: same fuel, same proof shape, and a round is expensive (see "the re-walk") |
| 2020 day 15 (memory game) | `Nat.iterate` over a `Game` with an `Array` updated in place | `(Stream.iterate takeTurn begin).at later` | **worse**: the stream would keep old games alive, so the `Array` write copies (argued); the array's size needs the turn count anyway |
| 2024 day 6 (guard) | `loopsFrom` with a `seen` set and a budget | `findRepeat` over the guard's turns | **worse**: it is the hot loop of part 2, run once per visited cell; the walk ends (she leaves the map), so it isn't an infinite stream |
| 2020 day 8 (handheld) | `runFrom` by a `decreasing` measure, no fuel | `findRepeat` | **worse**: the measure proves termination outright; a stream search needs fuel and a proof the fuel suffices |
| 2025 day 4 (paper rolls) | `settleRows` by a `decreasing` measure | iterate until stable | **worse**, for the same reason as 2020 day 8 |
| 2021 day 6, 2021 day 14, 2024 day 11, 2024 day 21, 2020 day 17, `Plane` turns | `Nat.iterate n step x` for a fixed n (6 to 256) | `(Stream.iterate step x).at n` | neutral: `Nat.iterate` already says it, and `at` is defined as it |
| 2021 day 17 (probe) | spec `after n velocity` by `Nat.iterate`; program `hitsWithin` stops early on `past` | spec `trajectory.at n`; program a `find` | neutral: the spec reads as well; the program's early exit doesn't fit `take`/`find` |
| 2024 day 14 (robots) | `List.range 0 period |> .find` | `Stream.fromFn … |> .find period` | neutral: the period is the natural bound, and the positions are a closed form |
| 2024 day 17 (machine) | `run` with `fuelFor` steps | a stream of machine states | neutral: the machine halts; the fuel is a proved bound, not a stand-in |
| 2020 day 13, day 19, day 20; 2024 day 15 | fuel or bounded searches over finite structure | none | not a sequence: streams don't apply |
| games/rogue `Random` | a handler threading an LCG seed | a handler reading a `Stream Nat` | neutral (see below) |

## How the costs were judged

Three facts about std's `Stream` decide most verdicts (from reading
`crates/elab/src/std/Stream/`):

- **`take n` and `at n` walk once.** `take` reads `base.walk n`, and `at`
  is `base.at`, which for `Stream.iterate` is `Nat.iterate`. A day that
  uses only these pays nothing over today.
- **The re-walk.** `head`/`tail` reading (and so `fold` and `find`, which
  are written with `head` and `tail`) refills its cells from the stream's
  origin when they run out, for twice the distance. For `Stream.iterate f
  x` that re-runs `f` from `x`: about 2n calls of `f` to read n values
  (argued from `Stream.Cells.refill`; the proposal's "about 4n steps"
  counts all steps). That is invisible for a cheap step (`nextSecret`) and
  a doubling of the work for an expensive one (a grid round).
- **The origin is kept.** A stream remembers its first value for the
  re-walk, and a cell's thunk holds the value it steps from. A state with an
  `Array` that today is updated in place (2020 day 15) would be shared, so
  each write copies (argued, not measured).

So the days that gain read their sequence with `take` or `at`, not by a
`head`/`tail` loop, and their step is cheap or run few times.

## The candidates

### 2021 day 11: genuine benefit (clearer, shorter)

`aoc/src/Aoc/Year2021/Day11/Day11.sw` steps the cavern in two loops:

```
def Cavern.flashesIn (cavern: Cavern): (steps: Nat) → Nat
  | Zero => 0
  | Succ more =>
    let next := cavern.step
    next.zeros + next.flashesIn more
…
def Cavern.firstSync (cavern: Cavern) (number: Nat): (steps: Nat) → Option Nat
  | Zero => None
  | Succ more =>
    let next := cavern.step
    if next.allZero then Some number else next.firstSync (Succ number) more
```

and `Proofs/Parts.sw` defines a third, `stepsFrom`, to talk about the
cavern after k steps. Both parts are questions about one sequence, the
cavern after each step:

```
def Cavern.afterSteps (cavern: Cavern): Stream Cavern := (Stream.iterate Cavern.step cavern).tail
def Cavern.solvePart1 (cavern: Cavern): Nat := cavern.afterSteps.take 100 |> .sumBy .zeros
def Cavern.solvePart2 (cavern: Cavern): Option Nat :=
  cavern.afterSteps.take syncLimit |> .findIndex .allZero |> .map (+ 1)
```

- *Clearer and shorter*: the two loops and `stepsFrom` go (about 15
  lines), and each part reads as the puzzle asks it.
- *Proofs*: `syncFound` and `syncNone` (about 45 lines of induction with
  index bookkeeping) become std's `List.findIndexSome`, `findIndexOf` and
  `findIndexNone` with `Stream.takeGet`; `stepsFrom cavern k` becomes
  `(Stream.iterate Cavern.step cavern).at k`, which is `Nat.iterate` by
  `Stream.iterateAt`. Estimated shorter, not certain: `findIndexNone`
  speaks of membership, part 2's "none up to the limit" of positions, and
  bridging those may cost what it saves.
- *Speed*: unchanged, since `take` walks once (argued).
- One `.tail` on an `iterate` stream is one refill, not a loop.

### 2024 day 22: genuine benefit (clearer, a little shorter)

`aoc/src/Aoc/Year2024/Day22/Day22.sw` evolves the same secret two ways:

```
def secrets: (count: Nat) → (secret: Nat) → List Nat
  | Zero, secret => [secret]
  | Succ count, secret => [secret, ..secrets count (nextSecret secret)]

def solvePart1 (buyers: List Nat): Nat := buyers.sumBy (Nat.iterate (count := 2000) (step := nextSecret))
```

and the spec has its own copy, `secretNumbers`, which the proof
`secretsMatch` ties to `secrets` by induction. The puzzle speaks of "the
sequence" of a buyer's secret numbers, and both parts read it: part 1 its
2000th new number, part 2 its first 2001 as prices. One stream says that:

```
def Buyer.secrets (buyer: Nat): Stream Nat := Stream.iterate nextSecret buyer
-- part 1: (Buyer.secrets buyer).at 2000; part 2: (Buyer.secrets buyer).take 2001
```

- *Clearer*: one definition of the sequence, used by both parts.
- *Shorter*: `secrets` goes; whether the spec's `secretNumbers` also
  becomes a stream is a choice (it reads as the puzzle's words now), and
  `secretsMatch` becomes `Stream.iterate`'s congruence from
  `nextSecretEvolves`, which std doesn't have yet.
- *Speed*: unchanged (`at` and `take` walk once).
- Small: a few lines either way. It is the clearest case of a day whose
  object *is* an infinite sequence.

### 2020 day 11: neutral

`Layout.settle` (`aoc/src/Aoc/Year2020/Day11/Day11.sw`) runs rounds until
one changes nothing, giving up after `roundLimit` (1000):

```
  | Succ more =>
    let next := layout.round plan
    if next == layout then Some layout else next.settle plan more
```

A stream version finds the first adjacent repeat in `Stream.iterate round`,
with the same limit. The proofs (`Proofs/Settle.sw`) already state settling
as `Nat.iterate rounds round start = final`, so they don't get easier, and
"nothing bounds the rounds in general" stays true. A round maps the whole
grid; read with `head`/`tail` it would run about twice (the re-walk). No
gain.

### 2020 day 15: worse

`Starting.numberSpoken` (`aoc/src/Aoc/Year2020/Day15/Day15.sw`) is the
`later`-th iterate of a turn, over a `Game` holding an `Array` the turn
writes in place:

```
    Nat.iterate later
      (game => game.say (starting.nextAfter count game))
      (Game.begin (starting.room turn) starting.numbers.head)
```

It is the nth term of a sequence, so a stream fits on paper. But the array's
size comes from the turn count (`room turn`), so the stream can't be built
without it, and the stream keeps its origin and the game each cell steps
from, so the `Array.set` that is O(1) now would copy the array every turn
(argued; 30,000,000 turns). `Nat.iterate` is the right tool.

### 2024 day 6: worse

`Sightlines.loopsFrom` walks the guard turn to turn, looking for a state in
`seen`, with `stateCount` as the budget. It is `findRepeat`'s shape, but
the walk ends when she leaves the map (`nextTurn` gives `None`), so the
stream would be of `Option Guard` with `None` forever after; and part 2 runs
it once per visited cell (thousands of times), where any per-step overhead
shows. The proofs (`Proofs/Loops.sw`) follow the recursion directly.

### 2020 day 8 and 2025 day 4: worse

Both stop by a measure, not fuel: `Code.runFrom` removes an instruction
from `unvisited` each step (`decreasing unvisited.size`), and `settleRows`
removes rolls each round (`decreasing countRolls rows`). That is better
than any stream search, which needs fuel and a proof that it is enough.
2020 day 8 is the puzzle "the first instruction run twice", the textbook
`findRepeat`, and still shouldn't use it.

### Fixed-count iteration: neutral

2021 day 6 (`Nat.iterate days Counts.nextDay …`, 80 and 256 days), 2021
day 14 (`Nat.iterate steps (stepCounts …)`), 2024 day 11 (`blinks.iterate
blinkCounts …`), 2024 day 21 (`Nat.iterate robots Costs.next Costs.yours`),
2020 day 17 (`Nat.iterate 6 Pocket.cycle`) and `Aoc.Common.Plane`'s turns
all take the nth state for a known n. `(Stream.iterate f x).at n` is defined
as `Nat.iterate n f x`, so it would only add a name.

### 2021 day 17: neutral

The spec's `after n velocity` is `Nat.iterate n move …`, and `Hits` is
`∃ n => Within target (after n velocity)`. `trajectory.at n` would read the
same. The program's `hitsWithin` stops as soon as the probe is `past` the
target; neither `take` nor `find` stops on a second condition, and its two
proofs (`hitsWithinSound`, `hitsWithinComplete`) are direct inductions.

### 2024 day 14: neutral

Part 2 searches `List.range 0 space.period |> .find (seconds => …
.isDistinct)`. The period (width times height) is the true bound, and
`positionAfter` is a closed form, so there is no step to iterate.

### 2024 day 17: neutral

`Machine.run` steps with `fuelFor registers program` fuel, a bound the spec
justifies (a loop shifting A right finishes). A stream of machine states
would need the same bound to stop.

### Not sequences: 2020 days 13, 19, 20; 2024 day 15

Their fuel bounds a search over finite structure: rule depth (2020 day 19),
a row of jigsaw tiles (2020 day 20), boxes in a line (2024 day 15), periods
within one bus's id (2020 day 13). Streams don't apply.

### games/rogue `Random`: neutral

`Random.withSeed` (`games/rogue/src/Rogue/Random.sw`) handles `next` by
threading an LCG state. A handler reading a `Stream Nat` instead
(`Stream.iterate lcg seed`, mapped to the top bits) would separate the
generator from the handler, and a theorem "for every stream" would cover
any source of randomness. But the proofs (`stepValid`, `stepApart`, …) are
already "whatever the seed", and a turn performs `Random` exactly once by
design (`Dice`), so nothing there reads a sequence. No gain now.

## Where streams don't help, plainly

- A loop with a termination measure (2020 day 8, 2025 day 4) is better
  than a stream search: no fuel, nothing to prove about it.
- A fixed number of steps is `Nat.iterate`; `Stream.iterate … .at n` is
  the same thing with a longer name.
- A hot loop with an expensive or in-place step (2020 day 15, 2024 day 6,
  2020 day 11) pays the re-walk, or the copies, for nothing.
- A walk that ends (the guard leaving, the machine halting) isn't an
  infinite stream.
- Proofs that need the step count keep `Nat.iterate`, and `Stream.at` of an
  `iterate` is that, so they gain nothing.

## Findings for std

- **No `Stream.findIndex`.** Part 2 of 2021 day 11 needs the position of
  the first value that passes, not the value; `find` gives the value. A
  `Stream.findIndex n p` with laws in terms of `at` ("the value there
  passes, none before does", and "none of the first n passes") would serve
  it better than `take` then `List.findIndex`, whose `None` law speaks of
  membership.
- **`fold` and `find` pay the re-walk; `take` doesn't.** Both are written
  with `head` and `tail`. Over `base.walk n`, whose cells are lazy, they
  would walk once and `find` would still stop early. For a stream of an
  expensive step that halves the work (argued). Worth a small ticket.
- **No congruence for `Stream.iterate`** (`f` and `g` agreeing everywhere
  give equal streams); `Quot.funext` gives it in a line, but a day shouldn't
  have to.
- `findRepeat` (SW-5003): no surveyed day should use it; the textbook cases
  (2020 day 8, 2024 day 6) are better as they are. That is no argument
  against having it, only that AoC's repeats here come with better tools.

## Recommendation

Rewrite **2021 day 11** first (the larger gain: two loops and two proofs
replaced by `take` and std's `findIndex` lemmas), then **2024 day 22** if
time allows (small, the clearest "the puzzle's object is a sequence"
case). Neither needs `findRepeat`, so phase 2 needn't wait for SW-5003.
Timing before and after should show no change, since both read with `take`
and `at`; if 2021 day 11 is written with `fold`/`find` instead, the
re-walk's doubling of `Cavern.step` should show, and measuring that is
itself useful for D3776.
