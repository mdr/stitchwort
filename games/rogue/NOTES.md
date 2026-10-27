# Friction report: a roguelike in Stitchwort (stage 1)

What was awkward, missing or surprising while writing `games/rogue/` (D1244),
roughly in the order it came up, then ranked at the end. Compiler built from
`main` at fa6c57ce, 25 October 2026.

## The program

### 1. `∈` on a list of my own records isn't decidable

```stitchwort
if target ∈ state.potions then …      -- state.potions: List Position
```

```text
[E-AUTO-NONE] Error: no way to decide `List.Any (y => y = target) state.potions`
  Note: a `Bool` is expected here, and a proposition is turned into one only if it has a decision procedure
```

`Position` is a plain record with a derived `DecEq`, and the guide's own
example is `xs.filter (x => x ∉ seen)` (on `Nat`). So membership is decidable
for `Nat` but not for a derived `DecEq` type. Workaround:
`state.potions.any (== target)`.

### 2. `% (most + 1)` needs a proof that `most + 1 ≠ 0`

```stitchwort
def Dice.upTo (dice: Dice) (index: Nat) (most: Nat): Nat :=
  (lcg (lcg (dice.seed + index * 7919)) / 65536) % (most + 1)
```

```text
[E-AUTO-STUCK] Error: can't decide `most + 1 ≠ 0` here
  it depends on values that aren't known until the program runs
```

`most + 1` computes to `Succ most`, which is never 0, and writing
`% Succ most` is accepted. The `auto` search doesn't see it through `+ 1`,
and the message ("depends on values that aren't known") is wrong for this
case: no value needs to be known.

### 3. No helpers of my own in `List`'s namespace

```stitchwort
def List.pickFree (choices: List Position) …   -- to call choices.pickFree …
```

```text
[E-STD-NAMESPACE] Error: `List` is a namespace of the standard library, which a program can't add to
```

So a helper over a std type can't be called with a dot; it's
`pickFree choices player others`, and a pipeline that uses it stops reading
left to right. Scala's extension methods or Kotlin's extension functions are
the familiar alternative. The error is clear, at least.

### 4. Handlers can't wrap partial code, so the game loop counts down fuel

The natural loop is `Partial` (a game ends when the player says so). But a
handler can't go around partial code (chapter 8), and the game runs inside
three handlers: `fromLines` (input), `Random.withSeed` (randomness) and, in tests,
`IO.simulate`. So `play` takes a fuel argument:

```stitchwort
def maxTurns: Nat := 100000

def play: Nat → State → {IO, Input, Random} State
  | 0, state => state
  | Succ remaining, state => …
```

That's the choice the brief asked about: bounded, because only a total loop
can be handled, and so tested through `IO.simulate`. The alternative, a
`Partial` main with the seed kept in the state and no `Random` ability, would
have lost the ability and the scripted test. The cost is small, but every
interactive program will hit this.

### 5. `IO.print` always ends the line; no flush, no raw keys

A frame is one `print`: the ANSI clear (`"\u{1b}[2J\u{1b}[H"`, the `\u{…}`
escape works) glued to the map lines joined with `'\n'`. That works, but the
cursor always sits on the line below the message, and there's no way to print
a prompt (`> `) and read on the same line. Input is a line at a time, so each
move needs Enter; `Input` is an ability of its own so a key-at-a-time reader
can replace `fromLines` later. Checked that both runtimes are interactive: a
frame appears as soon as its line is typed, natively and with `--js`.

### 6. No seed source: no clock, no arguments, no environment

`IO` has `print`, `readLine` and `readAll`. `stitchwort run` passes no
command-line arguments to `main`, so the seed is a constant
(`defaultSeed = 2026`) and every game is the same game. A `--` argument list
or an `IO.time`/`IO.randomSeed` operation would do.

### 7. `IO.simulate` needs an import that `IO.print` doesn't

`IO.print` and `IO.readLine` are in the prelude; `IO.simulate` isn't:

```text
[E-UNKNOWN-NAME] Error: unknown name `IO.simulate`
  Note: `IO.simulate` needs `import Std (IO)`
```

The note says exactly what to do, but it's surprising that half a namespace
is in scope.

### 8. Constructors with the same name in two types are ambiguous everywhere

```stitchwort
type Command = | Move | Quit
type Phase = | Playing | Quit

def phaseOf: Command → Phase
  | Quit => Quit        -- E-AMBIGUOUS, in the pattern and in the result
```

Even in a pattern whose type is known from the signature. I renamed the phase
`GaveUp`. Rust, Scala 3 and Lean would resolve both from the expected type.

### 9. No or-patterns

```stitchwort
def commandOf (key: Char): Option Command :=
  match key with
    | 'k' => Some (Move North)
    | 'w' => Some (Move North)
    | 'j' => Some (Move South)
    | 's' => Some (Move South)
    …
```

`| 'k' | 'w' => …` would halve it.

### 10. A tuple parameter needs three brackets

```stitchwort
dungeonRows.withIndex.map (((row, chars)) =>
  chars.withIndex.map (((column, char)) => glyphAt state { row, column } char) |> Text.fromList)
```

One for the argument, one for the pattern, one for the tuple. And a 2-D
`withIndex` is two nested ones, with a record annotation where the cell's
position is built: `(({ row, column }: Position), char)`. A `mapWithIndex`
(`(i x) => …`) would help.

### 11. The formatter mis-indents a record update after `let`s

```stitchwort
    let events := …
    {
      state |
      monsters = outcome.moved,
      hitPoints,
      …
    }
```

`stitchwort fmt` turns the first field into `        monsters = …` (two
columns further than its siblings), and keeps doing it on every run. Not
caused by the punned field (`hitPoints = hitPoints` does the same). I moved
the `message` and `phase` into `let`s so the update fits on one line. The
formatter also doesn't wrap long lines, so a 200-column line is left alone.

### 12. Small things

- `Text.join` takes a `Char` separator (`Text.join lines '\n'`), not a `Text`.
  Fine here; a `", "` separator would need `List.intersperse` and `concat`.
- A text block's trailing newline is dropped by putting the closing `"""`
  right after the last character: handy, but easy to miss when comparing
  frames.
- Ability operations are short names in the namespace (`next()`), so
  `Random.next()` and `next()` both work; I used the short one, which reads
  oddly out of context.

## The proofs

The three invariants (player never in a wall, hit points never above the
maximum, no monster on the player's cell) are proved for every state, command
and seed, about `step` as the seeded handler runs it (Proofs/). That went far
better than expected: about 240 lines, each lemma through in one or two attempts, and no axioms
(`stitchwort axioms Rogue.Proofs.stepValid` prints nothing). What helped:

- **Handlers compute.** `Random.withSeed seed (() => step state command)` is
  *definitionally* `resolve { seed = lcg seed / 65536 } state command`, so
  `rfl` proves it and the theorems about `step` are one line each.
- **`match h: cond with` on a `Bool` condition** generalises it in the goal,
  so each branch of the program's `if` computes, exactly as in the guide's
  `clampTo` example.
- **Record updates, `List.map` and `List.filter` compute in goals**, so
  `(attack dice state monster).player` is `state.player` with no lemma.

What hurt:

### 13. The design bends to keep handlers provable

A turn draws exactly one random number and derives all its rolls from it
(`Dice`), *because* a handler applied to a computation of known shape computes,
but one that draws once per monster has a data-dependent shape: proving
anything about it would need induction over everything the computation does,
which `match reify` can't do yet ("it splits once"). One draw per turn is a
reasonable design anyway, but I chose it for the proofs.

### 14. Goals unfold top-level constants

A goal that mentions `isWall` shows the whole dungeon:

```text
stairs: Decidable.toBool (Char.decEqFrom (List.getOr (List.getOr [['#', '#', '#', …
```

30 KB of output for six goals; I had to `grep` for the `⊢` lines. Showing
`isStairs state.player = True` (the definition folded, as written in the
`match`) would be far more readable.

### 15. `_` for an intermediate record couldn't be inferred

```stitchwort
actAllClear dice player (index + 1) _ waiting (clearSnoc …) rest
```

```text
expected `Rogue.monsterAt player (?0 dice player index outcome …).moved = None`,
but this has type `Clear player (List.append outcome.moved [monster])`
```

The `_` is the record the program built inline, and only its `moved` field is
constrained, so unification can't solve it. I refactored the program (an
`Outcome.add` helper) so the proof could name the value:
`(outcome.add monster _ _)`. A better program, as it happens, but the proof
drove it.

### 16. Things proved only by example

- That the whole game (`play`, through `IO` and `Input`) keeps the invariants
  is induction on turns over `stepValid`; I didn't state it, since `play` is
  effectful and its loop is inside three handlers. `stepValid` plus
  `initialValid` is the content.
- Monsters never overlap each other: the program checks it (`pickFree`), and a
  test checks one case; not proved.

## Tests

47 tests: walls, doors, combat (fixed dice: a blow of 2, 3 and 4), monsters
hitting back, death, potions (capped heal), the stairs, keys, the generator,
and play-throughs through `IO.simulate` (a winning route on the default seed,
end of input, skipped keys, several commands per line, and the first frame
compared with a text block). Property-style checks are `(List.range 20).all`;
proper property tests would be nicer.

## Performance

No trouble. A 57-turn game (58 frames of 44 by 11, monsters, rendering)
including the check: 0.23 s natively, 0.32 s with `--js`. Checking the whole
project from cold, proofs included: 1.2 s; checking and running all 47 tests from cold: 1.4 s.

## Ranked: the top ten

1. Handlers can't wrap partial code (4): every interactive loop needs fuel.
2. `IO` can't print without a line ending, read a key, or seed (5, 6).
3. Goals unfold top-level constants into pages of output (14).
4. `∈` isn't decidable on lists of derived-`DecEq` records (1).
5. Same-named constructors are ambiguous even where the type is known (8).
6. Helpers on std types can't be dot-called (3).
7. Formatter mis-indents a record update after `let`s (11).
8. `% (n + 1)` isn't seen to be safe (2), with a misleading message.
9. No or-patterns (9); the triple-bracket tuple lambda (10).
10. Proof-driven design: one random draw per turn, and refactoring so a proof
    can name an intermediate value (13, 15). `IO.simulate`'s missing import (7).

# Stage 2: generated levels, items, chasing

Generated levels (six rooms in a 3 by 2 grid of sections, joined by a snake
of corridors and sometimes one more), three levels down to an amulet,
potions carried and drunk with `p`, swords, trolls, and a fourth invariant
(no monster in a wall). Compiler built from `main` at 4eb90fe0, 25 October
2026. New friction, most costly first.

## 1. A handler run inside the pure turn sank every proof about the turn

`>` first made the next level on the spot, inside `resolve`, by running the
generator under a handler of its own, so that the turn still drew one number:

```stitchwort
def descend (dice: Dice) (state: State): State :=
  let arrived := arrive state (Random.withSeed dice.seed (() => generateLevel depth))
  …
```

Every theorem about `resolve` then failed, including those whose proof
never reaches the `Descend` branch:

```text
[E-RESOURCE] Error: ran out of resources: a value was too large to show
 28 │ ╭─▶ theorem resolveOutOfWalls (dice: Dice) (state: State) (command: Command) (inside: …
    │ ╰──── while checking this
    │     Note: this isn't a type error or a failed test: there's no answer within the limits
```

and the first attempt at the `Descend` case itself ran for over two minutes
before I stopped it. With the generator call replaced by `state`, the same
proofs checked at once, so the generator is the cause; which part of the
checker runs it (the `match` looking for occurrences in the goal, or the
counterexample search) I didn't establish. All levels are now made when the
game starts, at the edge (`newGame`), and kept in `State.below`: a sound
design, but the checker chose it, not me. A way to mark a definition opaque
to the checker (Lean's `@[irreducible]`) would have let the first design
stand.

## 2. `n / 2 ≤ n` is out of `omega`'s reach, and std has no lemma for it

```text
[E-OMEGA] Error: `omega` can't prove `Nat.divFuel n n 2 ≤ n`
  Note 2: atoms: `Nat.divFuel n n 2`, `n`
```

Division shows up unfolded to its fuel function. The proof is
`omega [Nat.divMulLe n 2 (twoIsZero => omega)]`: findable, but `Nat.divLe`
(`n / d ≤ n`) belongs in std, and `omega` could know division by a literal.

## 3. A sub-namespace can't add helpers to its parent's types

```text
[E-FOREIGN-NAMESPACE] Error: `Area` belongs to namespace Rogue, and Rogue.Tests can't add to it
 44 │ def Area.fits (area: Area): Bool :=
```

Stage 1's item 3 was about std's types; this is the program's own type, from
its own tests. So it's `fitsOnScreen area`, not `area.fits`.

## 4. Small inference gaps

- `let player := { row = 1, column = 10 }` needs `: Position`, though only
  one record type in scope has those fields.
- `let awayFromEntrance := () => room (…roll 4…)` is `E-CANNOT-INFER` ("add
  a type annotation"); I inlined it. Fixed: a lambda's body now works out
  its abilities, and `generateLevel` has `awayFromEntrance` back.
- `playGame newGame()` is `(playGame newGame)()`, reported as "this isn't a
  function … its type is `Rogue.State`"; it needs `playGame (newGame())`.
- `List.lookup` takes the equality decision as an argument
  (`marks.lookup column decEq`), so I used `find` on the pairs.

## 5. An unexplained "recursed more deeply than allowed"

To find the scripted winning route I wrote a throwaway bot (a search from
the target each turn, run inside `Random.withSeed`). On level 2 it stopped with

```text
[E-RESOURCE] Error: ran out of resources: it recursed more deeply than allowed
 54 │ def main(): {IO} () :=
    │     ╰─── while running this program
```

The search's step was
`frontier.flatMap neighbours |> .dedup |> .filter (…)`, then a `foldLeft`
to record the new cells; rewriting it as one `foldLeft` over the
neighbours made it run, with the same result as before on level 1. `dedup`
alone isn't it (`(List.range 5000).dedup` is fine in a test), so I don't know
what recursed; perhaps something about running under a handler. The error
doesn't say which function was deep. (In the same bot, `Map.getOr` takes the
fallback before the key, so `distances.getOr key 100000` type-checked and
returned the key: a `Nat`-for-`Nat` slip that named arguments would catch.)

## 6. Long values are cut off in test failures

A failing `==` shows `left: "############       ####…`, so a test can't show
a whole frame, and a test has no way to print. I looked at frames from a
throwaway `main` instead.

## What went well

- **Invariants as `List.All`.** "No monster in a wall" is
  `List.All (monster => isWall level monster.position = False) monsters`, and
  std's `List.allAppend`, with `Both` and `Trivial` as patterns, kept its
  proofs (the monsters' turn, a blow, placing a new level's monsters) short.
  Each went through at the first or second try, as did the stage-1 proofs
  with the level threaded through.
- **Properties true of every value.** The start is the middle of the level's
  `entrance` room, and `isFloor` checks the entrance first, so
  `startOnFloor (level: Level)` holds for *every* level, generated or not,
  in three lines. `arrive` re-checks the generator's placements with
  `pickFree`, so its theorems hold whatever the generator planned. No proof
  looks inside the generator.
- **`Random.withSeed` in tests.** `Random.withSeed seed (() => generateLevel depth)` is the
  generator's output for a seed, in a pure test, so checking 40 seeds at
  every depth for reachability is a few lines.

## Not proved

That the goal can be reached from the start. Floor is a union of rectangles,
and a proof would need paths and connectivity over them. Tested instead: a
depth-first search over the cells on 40 seeds at every depth, and every
floor cell reachable on 10 seeds. Also unproved, as in stage 1: no two
monsters share a cell (tested on every generated level and in a chase).

## Tests and speed

94 tests: the stage-1 unit tests moved to a hand-made two-room level;
chasing (closing in, the longer gap first, round rock, down a corridor, not
out of sight, a pack without sharing cells); items (potions carried and
drunk, swords, the amulet); the stairs; the generator over 40 seeds by 3
depths; placement by hand; and a 232-turn winning game through all three
levels via `IO.simulate`, with its first frame compared. All 94 from cold,
proofs included: 6.9 s on a heavily loaded machine (load average over 100).
A 36-turn game runs in 0.25 s; each level's rock is drawn once, when it's
made, and a frame only overlays what stands on it.

## Ranked: stage 2

1. A handler inside the pure turn made the checker unfold the generator in
   every proof about a turn (1).
2. `omega` and std don't know `n / 2 ≤ n` (2).
3. An unexplained runtime recursion limit, with no hint of where (5).
4. Sub-namespaces can't add helpers to the program's own types (3).
5. Small inference gaps, and long values cut off in failures (4, 6).

# Stage 3: keys, frames and no fuel

The shell moved onto std's `Terminal` (docs/proposals/terminal-io.md §8,
lane 5), on handlers that run partial code
(docs/proposals/partial-handlers.md). `play` reads one keypress per turn
(arrows as well as `hjkl`/`wasd`), draws whole frames through
`Terminal.draw`, and loops with no bound; `main` seeds the game from
`IO.randomSeed`, so each run is a different dungeon. The pure core, the
generator and every proof are untouched, and `stitchwort axioms` reports
no axioms for `stepValid`, `stepAtMost`, `stepOnFloor`, `stepOutOfWalls`,
`stepClear`, `withSeedStep` and `startingValid`.

## What got simpler

- **No fuel.** `maxTurns`, its comment explaining why the loop wasn't
  `Partial`, the `| 0, state => state` case and the "ran out of turns"
  ending are gone. `play` is the loop as one would write it: `{Terminal,
  Random, Partial}`, with `Random.withSeed` and `Terminal.toIO` wrapped round it
  unchanged.
- **No reading loop of our own.** Stage 1's `fromLines`/`nextFrom`/
  `readCommands` (with `linesPerCommand`, a second bound on blank lines)
  were 30 lines. Now `nextCommand` is one `Terminal.readKey` and a
  `match`; a key that isn't a command just loops (`None => play state`),
  which needed fuel or a counter before. The `Input` ability went too:
  `Terminal` is already the seam it stood for, and `Terminal.simulate` is
  the test handler, so the game needs no handler of its own for input.
- **Tests on frames, not printed text.** `Terminal.simulate` gives each
  frame as its lines, so the first-frame test no longer strips a clear-screen
  prefix and splits a printed text, and the winning game is the stage-1
  route joined into one key script.

## New friction

1. **`IO.simulate`'s seed is 0, so the whole `main` can't replay the
   winning route.** The route is for seed 2026. `main` is split into
   `IO.randomSeed` and `playOn seed`; the winning test goes through
   `IO.simulate` and `toIO` via `playOn testSeed`, and only a short quit is
   run through `main` itself. An `IO.simulateWith { seed }` (or a seed
   argument) would let a test drive the real `main`.
2. **Piped frames keep their colours.** Fixed: `Frame.plain` strips colour codes, and `Terminal.simulate` records the stripped lines (what a pipe shows); tests compare plain lines. A test that wants the colours checks the coloured `frame` function directly.
3. **`|>` binds looser than `∧`.** `a ∧ xs.filter p |> .length == 4` pipes
   the whole conjunction, and the error ("expected `Bool`, but this has type
   `List Text`") points at the filter, not the pipe. Brackets fixed it.
4. **`Char.toText` needs `import Std (Char)`**, though `Char` itself is in
   the prelude; the error says so, with the fix.
5. **Two generators.** The game keeps its own LCG (`Rogue.Random`) and only
   takes its seed from `IO.randomSeed` (cut to 31 bits). Moving to std's
   SplitMix64 would change every seeded value the tests pin (the 232-turn
   route, the first map) and `withSeedStep`'s statement, for no gain in play.
6. **On a terminal each line ends CR CR LF.** In the pseudo-terminal check,
   `Frame.ansi`'s CR LF arrives as `\r\r\n`: keys mode seems to leave the
   terminal's output translation of LF on. Harmless to the eye.

The tests: 99, all through `Terminal.simulate` or `IO.simulate`, 11 s from
cold on a loaded machine.

# Opaque definitions: levels made on the stairs

Stage 2's workaround is gone (docs/proposals/opaque-definitions.md §7).
`generateLevel` is an `opaque def`, and `descend` makes the next level from
the turn's dice under `Random.withSeed`, as the first design did:

```stitchwort
def descend (dice: Dice) (state: State): State :=
  let plan := Random.withSeed dice.seed (() => generateLevel (state.level.depth + 1))
  …
```

`State.below` and the up-front level making in `newGame` are removed
(`newGame` is `startingState (generateLevel 1)`). Every theorem about a turn
checks again with no `unfolding` anywhere: `stepValid`, `stepAtMost`,
`stepOnFloor`, `stepOutOfWalls`, `stepClear`, `stepApart` and `withSeedStep`
are word for word as before. What changed are the five `descend…` lemmas:
they dropped the `match state.below` and gained the `dice` argument. The
three that care about the new level apply the generic lemmas to
`Random.withSeed dice.seed (() => generateLevel (state.level.depth + 1))`
(`startOnFloor`, `placeMonstersClear`, `placeMonstersApart`,
`placeMonstersOnFloor`); the hit point ones are `rfl` and `atMost`.

What did not get easier is linking `goalReachable` to `generateLevel` (see
PROOFS.md, "Tried").

Tests: levels are now made from the turn's seed, so the scripted game, its
frames and the stairs test were re-recorded (a 228-turn win on seed 2026,
found with a throwaway breadth-first-search bot driving `step`). The first
level and its first frame are unchanged. 100 tests.
