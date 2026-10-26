# What's proved about the roguelike

The proofs are in `src/Rogue/Proofs/`, checked by `task rogue:test`. Every
theorem named here is checked by the compiler for **every** input it
mentions (every seed, every command, every key, every level), not just for
examples, and `stitchwort axioms` reports that none of them uses an axiom.

This note lists what is proved, what was tried and didn't go through, and
what the language or std would need for the rest. It came out of an
exploration (25 Oct 2026) and a follow-up (26 Oct 2026) that linked the
proofs to the real generator; `NOTES.md` has the history before it.

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

### 3. The way down can always be reached (Reach.sw, Generated.sw)

| Theorem | In plain words |
|---|---|
| `generatedReachable` | **for every seed and depth**, on the level `generateLevel` makes under the seeded handler, there is a sequence of moves from the start to the stairs (or the amulet) that only ever steps onto floor |
| `planReachable` | the same for the level `planFrom` plans from *any* list of numbers |
| `goalReachable` | the same for the level `layOut` makes from any rooms, with entrance and exit numbered below 6 |
| `walkWithin` | inside a rectangle of floor, any cell can be walked to from any other (along the row, then along the column) |
| `corridorJoins` | the two ends of each corridor can be walked between, both ways |
| `hubJoins` | the corridors form a snake through all six rooms, so every room's middle can be reached from room 0's and back |

It holds for *any* rooms, wherever they are and whatever their size: the
proof only uses how corridors are drawn (middle to middle, along a row and
then a column) and which rooms they join. Monsters may stand in the way,
but walking into one attacks it, so nothing blocks the way for good.

How the link to the real generator works (Generated.sw): `generateLevel`
is now "draw, then plan": it draws every number it needs first
(`drawMore`, the same `next()` calls in the same order as before) and
plans the level from them with no randomness left (`planFrom`). So the
handler's part is a single fact, proved by induction on how many numbers
are drawn:

| Theorem | In plain words |
|---|---|
| `seededDrawMore` | drawing under the seeded handler and then finishing purely is finishing with the numbers `seededNumbers` lists (a pure function of the seed) |
| `generatedPlan` | so the plan `generateLevel` makes from a seed is `planFrom` of those numbers |
| `generatedHolds` | so whatever is true of every planned level is true of every generated one, for every seed and depth |
| `seededNewGame` | and the first state of the real program, `newGame()` under the seeded handler, is `startingState` of the level generated from that seed |
| `rollBelow` | a roll is below its bound: `roll most` under the seeded handler is at most `most` |

`planFrom` reads the rooms' numbers as remainders by 6, so its entrance
and exit are below 6 by `Nat.modLt`, with no fact about the handler
needed. `rollBelow` is the matching fact about `roll` itself, for
programs that still roll as they go.

### 4. Every level fits the screen, and everyone is drawn (Bounds.sw, Render.sw)

A level is *framed* (`Framed`) when its terrain is 20 rows of 66 cells and
every floor cell is among them. A state is *sound* (`Sound`) when it is
valid and its level is framed.

| Theorem | In plain words |
|---|---|
| `drawnPlayer` | in every sound state, the text `render` draws has `@` exactly at the player's row and column |
| `drawnMonster` | in every sound state, each monster's letter (`g`, `o`, `T`) is drawn exactly at its row and column |
| `newGameSound` | every new game, as the program starts it, is sound, for every seed |
| `replaySound` | any number of turns keeps a state sound |
| `generatedFramed` | every generated level is framed, for every seed and depth |
| `stepFramed`, `resolveFramed` | a turn keeps the level framed (it keeps the level, or goes down to a generated one) |
| `roomFits` | each of the six rooms fits inside its section, whatever the numbers |
| `corridorFits` | a corridor between two cells on the screen stays on the screen |
| `renderPlayer` | the text `render` draws has `@` at the player's row and column, for a player inside the terrain |
| `renderEveryMonster` | in a valid state, each monster inside the terrain is drawn at its row and column |
| `renderMonster` | the same without assuming validity: the cell shows the first monster standing there, unless the player is on it |
| `renderCell` | in general, each cell shows what stands on it (player first, then monsters, then items), or else the terrain |

So `drawnPlayer` and `drawnMonster` are `renderPlayer` and
`renderEveryMonster` with the inside-the-terrain assumption discharged for
every state a real game reaches.

### 5. Keys (Input.sw, Loop.sw)

| Theorem | In plain words |
|---|---|
| `arrowDecodes` | the bytes a terminal sends for each arrow key are read back as that arrow, whatever comes after (from std's `Key.nextBytes`) |
| `arrowMoves` | each arrow is the move in its direction |
| `documentedKeys` | h/j/k/l, a/s/w/d, `.`, `>`, `p` and `q` do what the keys line on screen says |
| `onlyListedKeys` | **no other printable key is a command**: a printable key that is a command is one of h/j/k/l, a/s/w/d, `.`, `>`, `p` and `q` (`commandKeys`) |
| `onlyCommandKeys` | and no other key at all: a key that is a command is an arrow, or one of those printable keys |
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

All keep the behaviour identical; the tests pass unchanged, including
the pinned first map and the winning game (232 turns before levels were made on the stairs, 228 after), which goes through all three levels.

- `play` was split into `play` (the loop) and `playTurn` (one key), so
  that one turn of the real loop is a total function (Rogue.sw).
- `generateLevel` builds its level with `layOut`, a pure function of
  the rooms and the rolls, with `corridorsOf` and `roomOf` named
  (Generate.sw).
- `generateLevel` is now `planFrom depth (drawMore [] (drawCount depth))`:
  draw every number first, then plan. `planFrom` takes roll *i* as number
  *i* of the draws, reduced as `roll` reduced it (`rollAt`: `% Succ most`),
  so the same `next()` calls are made in the same order and give the same
  level. `randomRoom`, `randomSpot`, `randomMonster` and `randomItem`
  became `roomFrom`, `spotFrom`, `monsterFrom` and `itemFrom`. `drawMore`
  adds each number at the end (`drawMore (drawn ++ [number]) rest`) rather
  than `Cons number (draws rest)`: see "language gaps" below for why.
- `layOut` and `drawCount` are opaque (only `goalReachable` and
  `planFramed` unfold `layOut`; nothing unfolds `drawCount`).
- None for the keys any more: `commandOfChar` is a plain `match` on
  characters (Input.sw). For a while it looked the key up in a table
  (`keyCommands`), because the catch-all arm of a character match couldn't
  be reasoned about; the language was fixed instead (see "Tried").

## Tried, and how far it got

| Candidate | Result |
|---|---|
| The whole loop `play` as one statement | **Not possible today, by design.** `play` is partial, and a partial program under a handler has nothing to prove about it (docs/proposals/partial-handlers.md §3.5). Two turns of `playTurn` do compute by `rfl` for any two keys; *n* turns would need induction over the handler, and `Terminal.simulate` hides its frame accumulator, so the state after one turn isn't `Terminal.simulate` of the rest. |
| No key but the documented ones is a command | **Proved, on the plain `match`** (`onlyListedKeys`, `onlyCommandKeys`). At first it couldn't be: a character pattern like `'k'` is a number pattern, compiled to a number case (`NumCase`) whose catch-all arm learned nothing about the character, and a number case on an unknown number never steps, so even knowing `code ≠ 107` for every listed code didn't reach the arm. The game looked keys up in a table instead (`keyCommands`, with std's `List.findSome`). Then the language was fixed (SW-533, docs/proposals/literal-match-facts.md): a catch-all arm now knows the value is none of the literals above it, so a proof's match on the same twelve characters has `commandOfChar` take its `_` arm in the proof's `_` arm, and the table went. Membership in `commandKeys` is decided with `Decidable.fromYes`, not `auto`, whose search stops 8 deep (the 7th key, `'w'`, is past what it finds). |
| `goalReachable` for `generateLevel` itself | **Proved** (`generatedReachable`), after three failures. (1) Unfolding the old `generateLevel` and passing `goalReachable` with holes: E-RESOURCE, the holes solved against the generator body run under the handler. (2) After splitting off `planFrom`, `planReachable` with `layOut` still transparent: E-RESOURCE, comparing `(planFrom depth numbers).level` with `layOut …` drew the terrain of a level with unknown rooms; fixed by making `layOut` opaque. (3) Then `generatedReachable` ran past 5 minutes: with an unknown depth, `drawCount depth` partly computes (`27 + 4 * (2 + 2 * depth) + …` still has some `Succ`s on the outside), so the handler starts drawing numbers symbolically; fixed by making `drawCount` opaque. Now all the proofs check in about 4 s of CPU. |
| Player and monsters inside the 20 by 66 terrain | **Proved** (`drawnPlayer`, `drawnMonster`, Bounds.sw), by the same route: every planned level is framed (`planFramed`, by `omega` on each room's rolls and a case per section), so every generated one is (`generatedHolds`), and a turn keeps the level or goes down to a generated one. |
| Winnability: a winning sequence of commands exists from the start | **Out of reach, and not true as stated.** Monsters roll their blows, so with unlucky seeds a game can be lost whatever the player does; "winnable" has to fix the seeds, and then it's a fact about one game. For a fixed seed it's the winning-route test, which is a unit test, not a proof. A real fairness theorem ("winnable with probability at least p") needs probability, which the language doesn't have. |

## What would be needed for the rest, ranked

1. **A frames-free or accumulator-exposing `Terminal.simulate`** (say a
   `Terminal.simulateFrom keys frames prog`), so that a proof can do
   induction over turns of a total loop (with fuel) and relate *n* turns of
   the real loop to `replay`. The one gap left between the proofs and the
   real loop: `replaySound` and `replayValid` give each turn its own seed,
   while the real loop threads one generator through every turn.
2. **Monad laws that compute, or without an axiom.** Under a handler,
   `f (g (p()))` and `(x => f (g x)) (p())` are different computations
   (`bind (bind p g') f'` against `bind p (x => …)`) unless `p` is known,
   and the law that joins them, `Effect.bindAssoc`, uses function
   extensionality, so `Quot.sound`. A first `seededDrawMore`, about
   `Cons first (draws rest)`, failed on exactly this (the step needs
   `seeded s (() => finish (Cons n (draws c)))` to be
   `seeded s (() => (rest => finish (Cons n rest)) (draws c))`). The
   workaround is to draw onto an accumulator, so that each step is the
   induction hypothesis on the nose, and to prove a second lemma
   (`seededDrawMoreThen`) for two pure steps after the drawing. Every
   program that runs a handler over "draw, then compute" will meet this; a
   rule that a pure function applied to a computation's result commutes
   with a handler (`seeded s (() => f (p())) = f (seeded s p)`, here
   `seededDrawMore`) would be worth having once, generally, for any deep
   handler of a state-like ability.
3. **Opacity is still something to discover by `E-RESOURCE`.** Two of the
   three failures above were a definition that was cheap to run and
   enormous to compare once its arguments were unknown (`layOut`'s
   terrain, `drawCount`'s partly-computed number). The goal-readback size
   cap (docs/proposals/goal-readback.md) addresses the first kind; the
   second was the kernel, not the read-back, and "ran out of resources"
   didn't say which definition was being unfolded. Naming the definition
   being unfolded at the time in the `E-RESOURCE` message would have
   saved a good part of the search.
4. ~~**Negative information in literal-pattern matches**~~ **Closed**
   (SW-533): the catch-all arm of a match on `'k'`, `'w'`, … now knows the
   character is none of them, and the game's `match` is back. A proof still
   needs an arm per character, as the program has.
5. **Small things met on the way** (each cost a few minutes):
   - `unfolding` after a signature that spans lines must be indented
     *less* than the type's continuation lines (as in docs/syntax.md);
     at the same indentation it's read as part of the type, and the error
     is "expected an expression, but found `unfolding`".
   - `then` can't be a parameter name (it's a keyword); the error says
     "expected a parameter's name, but found `then`", which is clear.
   - An `And` proof has no `.snd` (its fields are `left` and `right`); `And.right p`
     works.
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
