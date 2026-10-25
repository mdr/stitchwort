# What's proved about the roguelike

The proofs are in `src/Rogue/Proofs/`, checked by `task rogue:test`. Every
theorem named here is checked by the compiler for **every** input it
mentions (every seed, every command, every key, every level), not just for
examples, and `stitchwort axioms` reports that none of them uses an axiom.

This note lists what is proved, what was tried and didn't go through, and
what the language or std would need for the rest. It came out of an
exploration (25 Oct 2026); `NOTES.md` has the history before it.

## What's proved

### 1. Every game stays valid, however long

A state is *valid* (`Valid`, Valid.sw) when:

- the player isn't inside a wall;
- hit points are at most the maximum (12);
- no monster stands on the player;
- no monster stands inside a wall;
- **no two monsters stand on the same cell** (new: `Apart`, Apart.sw).

| Theorem | In plain words |
|---|---|
| `startingValid` | every new game starts valid, whatever levels the generator made |
| `arriveValid` | going down to any level the generator could make is valid |
| `resolveValid`, `stepValid` | one turn keeps a valid state valid, for every seed and command |
| `replayValid` (Game.sw) | **any number of turns** keeps it valid: for any list of (seed, command) pairs, playing them one after another from a valid state gives a valid state |
| `stepApart`, `resolveApart` | no two monsters share a cell after a turn |
| `monsterAtOwnCell` | so the monster found on a monster's cell is that monster |

### 2. The real game loop, one turn at a time (Loop.sw)

`play`, the loop the game runs, is now "repeat `playTurn` until the game
is over", and `playTurn` (read one key; if it's a command, take the turn
and draw the frame) is total, so it can be proved about. Under the test
handlers (`Terminal.simulate` for keys and frames, `seeded` for dice):

| Theorem | In plain words |
|---|---|
| `turnKey` | a key that is a command takes exactly the turn `resolve` describes, with that seed's dice, and draws exactly one frame: that turn's |
| `turnOther` | a key that isn't a command changes nothing and draws nothing |
| `turnEnd` | when the keys run out, the player gives up |
| `turnValid` | so every turn the real loop takes keeps the state valid |

The loop as a whole isn't proved (see "Tried" below); `replayValid` covers
any sequence of the turns it takes.

### 3. The way down can always be reached (Reach.sw)

| Theorem | In plain words |
|---|---|
| `goalReachable` | on every level the generator lays out, there is a sequence of moves from the start to the stairs (or the amulet) that only ever steps onto floor |
| `walkWithin` | inside a rectangle of floor, any cell can be walked to from any other (along the row, then along the column) |
| `corridorJoins` | the two ends of each corridor can be walked between, both ways |
| `hubJoins` | the corridors form a snake through all six rooms, so every room's middle can be reached from room 0's and back |

It holds for *any* rooms, wherever they are and whatever their size: the
proof only uses how corridors are drawn (middle to middle, along a row and
then a column) and which rooms they join. Monsters may stand in the way,
but walking into one attacks it, so nothing blocks the way for good.

The theorem is about `layOut`, the pure part of `generateLevel`, for room
numbers below 6. `generateLevel` picks them as `roll 5` and `… % 6`, which
are always below 6, but that link isn't machine-checked (see below).

### 4. Drawing (Render.sw)

| Theorem | In plain words |
|---|---|
| `renderPlayer` | the text `render` draws has `@` exactly at the player's row and column |
| `renderEveryMonster` | in a valid state, each monster's letter (`g`, `o`, `T`) is drawn exactly at its row and column |
| `renderMonster` | the same without assuming validity: the cell shows the first monster standing there, unless the player is on it |
| `renderCell` | in general, each cell shows what stands on it (player first, then monsters, then items), or else the terrain |

These need the cell to be inside the drawn terrain (20 rows by 66 columns);
that the player and monsters always are isn't proved (see below).

### 5. Keys (Input.sw, Loop.sw)

| Theorem | In plain words |
|---|---|
| `arrowDecodes` | the bytes a terminal sends for each arrow key are read back as that arrow, whatever comes after (from std's `Key.nextBytes`) |
| `arrowMoves` | each arrow is the move in its direction |
| `documentedKeys` | h/j/k/l, a/s/w/d, `.`, `>`, `p` and `q` do what the keys line on screen says |
| `arrowWalks` | end to end in the real turn: pressing an arrow, when the cell that way is floor with no monster on it, moves the player there |

`commandOf` being total needs no theorem: the checker rejects any
function that might not return.

### 6. Rules of a turn (Rules.sw)

| Theorem | In plain words |
|---|---|
| `resolveFinished` | once the game is won, lost or given up, nothing changes, whatever the command |
| `resolveQuit` | quitting gives up |
| `resolveMoves` | moving onto a free floor cell puts the player there |
| `monstersTurnHurt` | in the monsters' turn the player loses at most the sum of the strengths of the monsters **next to them** (a goblin's 2, an orc's 3, a troll's 4) |
| `monstersTurnHarmless` | so with no monster next to the player, the monsters' turn costs nothing |
| `resolveNoHeal` | hit points never go up, except by drinking |
| `resolveDrinkHeals` | and a potion heals at most 5 |

## Program changes

Both keep the behaviour identical; all 99 tests pass unchanged, including
the pinned first map and the 232-turn winning game.

- `play` was split into `play` (the loop) and `playTurn` (one key), so
  that one turn of the real loop is a total function (Rogue.sw).
- `generateLevel` now builds its level with `layOut`, a pure function of
  the rooms and the rolls, with `corridorsOf` and `roomOf` named
  (Generate.sw). The rolls are made in the same order.

## Tried, and how far it got

| Candidate | Result |
|---|---|
| The whole loop `play` as one statement | **Not possible today, by design.** `play` is partial, and a partial program under a handler has nothing to prove about it (docs/proposals/partial-handlers.md §3.5). Two turns of `playTurn` do compute by `rfl` for any two keys; *n* turns would need induction over the handler, and `Terminal.simulate` hides its frame accumulator, so the state after one turn isn't `Terminal.simulate` of the rest. |
| No key but the documented ones is a command | **Not proved.** A character pattern like `'k'` is a number pattern, and the catch-all arm of such a match learns nothing about the character (docs/syntax.md), so there's no way to show "anything else gives `None`" short of a case per character. |
| `goalReachable` for `generateLevel` itself | **Not attempted.** It needs the generator's output under `seeded`, which unfolds the whole generator (the stage-2 friction in NOTES.md), plus "a roll is below its bound" under the handler. |
| Player and monsters inside the 20 by 66 terrain | **Not attempted.** It's an extra invariant (floor stays inside the level), true because `randomRoom` keeps rooms inside their section; the same generator obstacle as above. With it, `renderPlayer` would need no hypotheses. |
| Winnability: a winning sequence of commands exists from the start | **Out of reach, and not true as stated.** Monsters roll their blows, so with unlucky seeds a game can be lost whatever the player does; "winnable" has to fix the seeds, and then it's a fact about one game. For a fixed seed it's the winning-route test, which is a unit test, not a proof. A real fairness theorem ("winnable with probability at least p") needs probability, which the language doesn't have. |

## What would be needed for the rest, ranked

1. **Opaque or sealed definitions** (in progress in a parallel lane). The
   first try of `goalReachable`, stated about `layOut` directly, ran out of
   resources (`E-RESOURCE`, "a value was too large to show"): checking it
   unfolded `Level.build`, whose terrain is a drawing of 20 by 66 cells.
   Stating the proofs about any `Level` with an equation for its corridors
   fixed it. Marking `Level.build`'s terrain (or `drawTerrain`) opaque
   would let the theorem be stated about `layOut` plainly.
2. **Proofs about the generator under its handler.** "A roll is below its
   bound" for any handler of `Random`, and a way to reason about
   `seeded seed (() => generateLevel depth)` without unfolding all of it,
   would link `goalReachable` to `generateLevel` and give the
   inside-the-terrain invariant.
3. **A frames-free or accumulator-exposing `Terminal.simulate`** (say a
   `Terminal.simulateFrom keys frames prog`), so that a proof can do
   induction over turns of a total loop (with fuel) and relate *n* turns of
   the real loop to `replay`.
4. **Negative information in literal-pattern matches**: in the catch-all
   arm of a match on `'k'`, `'w'`, …, knowing the character is none of
   them. That would prove "no other key is a command".
5. **Small things met on the way** (each cost a few minutes):
   - `|>` binds looser than `=`, so a theorem statement written
     `xs.map f |> .getOr d i = y` checks, but means "pipe into the
     equation"; it was only caught when the lemma was used. A warning for
     `|>` whose right side is a comparison would catch it.
   - An `_` for an argument passed to `omega` stays a metavariable, so the
     same term written with `_` and in full are different atoms; the
     monsters' event text had to be written out in full.
   - Pattern lambdas (`((row, chars)) => …`) can't take a type annotation;
     a typed `let` works.
   - A hypothesis named `at` broke `rewrite … at in …` with "the line
     starting with `in` is at or left of the enclosing block's column";
     renaming it fixed it, so `at` seems to be reserved, but the error
     doesn't say so.
   - No eta for records in conversion: `p = { row = p.row, column = p.column }`
     needs a match on `p`.
