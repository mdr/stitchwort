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
three handlers: `fromLines` (input), `seeded` (randomness) and, in tests,
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

- **Handlers compute.** `seeded seed (() => step state command)` is
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
