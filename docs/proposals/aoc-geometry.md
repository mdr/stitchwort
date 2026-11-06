# Proposal: a 2D geometry library for Aoc.Common that a day takes pieces from

**Status:** draft 1, 6 November 2026. Ticket SW-1617, from D2487 (Matt, 6 Nov 2026). It
rescopes SW-1484 (the plane library D2456 approved), which waits for this note, and folds
in SW-1474, SW-1475, SW-1587, SW-1588, SW-1592 and SW-1482. Decisions are
[§9](#9-decisions), Q1 to Q9; the orchestrator gives them D numbers.

**The short answer.** Keep the two worlds apart by type. Whole numbers from 0 (`Nat`) are
*places on a sheet*. Whole numbers that can go negative (`Int`) are *steps*, or places in a
plane with no edge. A day says which world it is in by the type it picks, not by a
setting. Which way y goes is the second question, and it gets two answers:

- **Rows and columns** (`Position`, `Offset`, `Grid`, as now) need no convention: "row"
  already means "counted down from the top".
- **x and y** need one, so the new `Int` type takes it as a type parameter:
  `Vector YUp` for maps and maths (2020 day 12's ship, 2021 day 17's probe), `Vector YDown`
  for screens and printed sheets, and `Vector Unoriented` when the puzzle has no up at all
  (2024 day 13's claw). Mixing two frames is a type error.

Directions don't depend on the frame. `Up` and `North` both mean "towards the top of the
picture as the puzzle draws it". Only the step from a direction to numbers asks the frame
what "up" does to y, and the turn lemmas are proved once for both frames (checked; see
[§3](#3-what-we-ran)). The pieces are separate modules, and a day imports the ones it uses.

This note can be read without knowing the code. Labels:

- **[checked]**: read in the code or docs at the place given, or in a source listed at the
  end ([R1] and so on);
- **[run]**: a scratch Stitchwort file checked with the release CLI in the main checkout
  (built 6 Nov 2026 09:58), on 6 November 2026. The files aren't committed; the code that
  matters is quoted;
- **[inferred]**: my reasoning from checked facts.

## Contents

- [1. The problem](#1-the-problem)
- [2. What the days do now (survey)](#2-what-the-days-do-now-survey)
- [3. What we ran](#3-what-we-ran)
- [4. How others do it](#4-how-others-do-it)
- [5. Options](#5-options)
- [6. The recommendation](#6-the-recommendation)
- [7. Before and after](#7-before-and-after)
- [8. Staged plan](#8-staged-plan)
- [9. Decisions](#9-decisions)
- [10. Evidence still to collect](#10-evidence-still-to-collect)
- [Sources](#sources)

## 1. The problem

Advent of Code has a lot of 2D puzzles: 28 of the 71 days in `aoc/src/Aoc` use 2D or 3D
coordinates ([§2](#2-what-the-days-do-now-survey)). Aoc.Common serves the *grid* puzzles
well: a `Position` is a row and a column (`Nat`s), an `Offset` is a step in rows and columns
(`Int`s), `Direction` is up, right, down or left, and `Grid` holds rows of cells, with about
60 lemmas [checked: `aoc/src/Aoc/Common/Grid.sw`, `Offset.sw`, `Proofs/`]. Then there is
`Point { x: Nat, y: Nat }` with `Line`, for puzzles that print `x,y`, with y going down
[checked: `Common/Point.sw:1`].

Three kinds of puzzle don't fit:

1. **A plane with no edge, where y goes up.** 2020 day 12's ship goes east and north, so its
   coordinates go negative, and it turns its waypoint by quarter turns. The day wrote its own
   `Location { east, north: Int }` and `Heading`, about 35 lines, and 81 lines of turn lemmas
   (Turns.sw) [checked: `Year2020/Day12/`; `aoc/NOTES-2020.md`, day 12 item 1]. 2021 day 17's
   probe falls under gravity, with y going up; it keeps raw `x`, `y`, `dx`, `dy` fields and a
   target `{ left, right, bottom, top }` [checked: `Year2021/Day17/Day17.sw:40`].
2. **A plane where up doesn't matter.** 2024 day 13 solves two linear equations in X and Y.
   It declared its own `Offset { x, y: Int }`, which hides Common's `Offset` (rows and
   columns) under the same name [checked: `Year2024/Day13/Day13.sw:23`].
3. **Grid extras each day writes again**: eight directions (2020 day 11's `compass`, 2024
   day 4's spec), a ray to the edge (2020 day 11), compass headings that map to `Direction`
   (2024 day 16, 31 lines), Manhattan distance (2020 day 12, 2024 day 20), rotating and
   flipping a picture (2020 day 20, 309 lines of proofs, about 120 of them general).

Two things make the obvious fix ("add an `Int` point with y up", D2456) awkward. Common's
`Point` already has `x` and `y` with y going *down*, so a second `x`/`y` type with y going
*up* would read the same and mean the opposite. And `Int` everywhere throws away what `Nat`
gives the grid days: a position can't be negative, so off the top edge is `None` and never a
wrong index. Matt (D2487): "it's nice to be able to distinguish between nat and int worlds",
and "what is up and down when Y might have different conventions", and he wants "a flexible
library that doesn't … overcommit you", from which "the Advent of Code problems could pick
what they need that … fits their frame of the world".

## 2. What the days do now (survey)

Every day in `aoc/src/Aoc` (2020 days 1 to 20, 2021 days 1 to 18, 2024 days 1 to 24, 2025
days 1 to 9) was searched for coordinate types, and the 2D days' programs, specs and proofs
were read [checked]. "y" is which way the puzzle's second coordinate goes. "Common lemmas" are
Aoc.Common lemmas the day's proofs cite.

| Day | Types it uses or defines | Nat/Int | y | Proofs about the geometry |
|---|---|---|---|---|
| 2020 d3 | `Grid Square`, `Position`; own `Slope { right, down }` | Nat | down | parse rectangle, `lookupOr` |
| 2020 d11 | `Grid Seat`, `around`; own `compass` (8 `Offset`s), `firstSeat` (a ray) | Nat + Int | down | `countAround`, `lookupAt`; Sight.sw 140 lines, 70 generic |
| 2020 d12 | own `Heading` (N/E/S/W), `Location { east, north }`, `rotated`, `manhattan` | Int | up | own Turns.sw, 81 lines |
| 2020 d17 | `Grid` for the slice; own `Cube { coordinates: List Int }` (3D, 4D) | Int | n/a | own neighbour counting |
| 2020 d20 | own `Image` (rows), `rotate`, `flip`, `orientations`, `edges`; `Set (List Nat)` for places | Nat | down | own Orientations.sw, 309 lines |
| 2021 d2 | own `Submarine { horizontal, depth }` | Nat, Int | down (depth) | none |
| 2021 d5 | `Point`, `Line`, `Line.points` | Nat | either | 37 theorems, own |
| 2021 d9 | `Grid (Fin 10)`, `neighbours`, `Grid.graph` | Nat | down | `neighbourAdjacent`, `adjacentNeighbour`, cell lemmas |
| 2021 d11 | `Grid Nat`, `around` | Nat | down | `aroundTouching`, `touchingAround`; own `countAround` (SW-1482) |
| 2021 d13 | `Point`, own `Fold`; `toPosition` to draw | Nat | down ("fold up") | `cellAt` |
| 2021 d15 | `Grid (Fin 10)`, `boxGraph`; own `RiskMap { height, width, … }` | Nat | down | `wrapSmall`, `wrapLarge`, `lookupOrAt` |
| 2021 d17 | own `Target { left, right, bottom, top }`, `Velocity { dx, dy }`, `Probe { x, y, dx, dy }` | Int | up | own, by `omega` |
| 2024 d4 | own `Grid { rows }`; spec's own `Direction { down, across: Step }` (8) | Nat | down | own (row windows) |
| 2024 d6 | `Position`, `Direction`, `turnRight`; own `Lab { height, width, … }` | Nat | down | `positionExt` |
| 2024 d8 | `Position`, `Offset`, `minus`, `offset`; own `divideBy`, `stepToward`, `City { height, width, … }` | Nat + Int | down | `offsetSome`, `offsetOf` |
| 2024 d10 | `Grid (Option Nat)`, `neighbours` | Nat | down | `neighbourAdjacent`, `neighboursDistinct` |
| 2024 d12 | `Map Position Char`, `Direction`; own `Position.diagonal`, quadrants | Nat | down | `memDirections`; own side counting |
| 2024 d13 | own `Offset { x, y: Int }` (hides Common's name) | Int | none | own (Cramer's rule) |
| 2024 d14 | `Position` read from `p=x,y`, `Offset` velocity, `Position.wrap`; own `Space { width, height, … }`, `Quadrant` | Nat + Int | down | `wrapWithin`, `wrapIterate` |
| 2024 d15 | `Cell := Offset` (a board with no edge), `Direction` | Int | down | `offsetStep*` (four lemmas) |
| 2024 d16 | `Position`; own `Heading` (E/S/W/N), `clockwise`, `toDirection` | Nat | down | `stepOpposite` |
| 2024 d18 | `Position` read from `x,y`; own `MemorySpace { size, … }`, `stepGraph` | Nat | down | own |
| 2024 d20 | `Position`, `Direction`; own `Position.distance` (Manhattan), `diamond` | Nat | down | `memDirections` |
| 2024 d21 | own `Position { row, column }` and own `Direction`: doesn't import Aoc.Common | Nat | down | own |
| 2025 d4 | own `Grid` of `Vec`s (sized, for speed) | Nat | down | own |
| 2025 d7 | own `Manifold` of `Vec Bool width` rows, `Hit { row, column }` | Nat | down | own |
| 2025 d8 | own `Point { x, y, z }` (3D; hides Common's name) | Nat | n/a | own |
| 2025 d9 | `Point`, `Line`; own `Rectangle { corner, opposite }`, compressed `Floor` | Nat | either | `cellAt` |

**Counts** [checked, counted by hand from the table]:

- 28 days use coordinates: 5 in 2020, 7 in 2021, 12 in 2024, 4 in 2025.
- **Nat grids (rows and columns)**: 19 days. Common's `Position` serves 13 of them; 2024
  d21 and 2025 d4 and d7 have their own, and 2024 d4 and 2020 d20 use plain rows.
- **Nat `x,y` sheets**: 3 days on Common's `Point` (2021 d5, d13, 2025 d9). 2024 d14 and d18
  read `x,y` straight into a `Position`.
- **Int planes**: 3 days (2020 d12, 2021 d17, 2024 d13), plus 2024 d15's board with no edge
  (on `Offset`) and two in more dimensions (2020 d17, 2025 d8).
- **y**: down in 23 days, up in 2 (2020 d12, 2021 d17), no up at all in 3 (2021 d5,
  2024 d13, 2025 d9).
- **Duplicated code** [inferred from the lines read]: 4 direction or heading types of a day's
  own (2020 d12, 2024 d4, d16, d21); 3 types that hide a Common name with different fields
  (2024 d13 `Offset`, d21 `Position`, 2025 d8 `Point`); 5 records that carry a height and a
  width (2021 d15, 2024 d6, d8, d14, d18); Manhattan distance twice; eight directions twice;
  quarter-turn code and lemmas once (about 120 lines with the spec's); picture rotation once
  (about 120 general lines). About 370 lines in all, most of them proofs.

What the table says [inferred]. The grid world is the common case and it works; its gaps are
extras (eight directions, rays, distance, rotation), not its types. Up and down matter in
only two days, and both have y going up; but every `x,y` sheet has y going down, so the
library meets both. No day uses a generic number type, and every geometry proof in the
corpus ends in `omega`, `cases` or `ring` on concrete `Nat`s and `Int`s.

## 3. What we ran

Scratch files in the session's scratchpad (`geometry/frame.sw`, `plane.sw`, `box.sw`,
`generic.sw`), checked with `stitchwort check` and `stitchwort test` [run]:

1. **A frame as a type parameter works.** A record with a parameter it doesn't use, `type
   Vector (f: Type) = { x: Int, y: Int }`, gets `==`, `Set (Vector YUp)` and `Vector.ext`
   as any record does. An interface on the frame carries the one number that differs:

   ```stitchwort
   interface Frame (f: Type) = { up: Int, unit: up * up = 1 }
   type YUp = | YGrowsUp
   type YDown = | YGrowsDown
   instance YUp.instFrame: Frame YUp := { up = 1, unit = rfl }
   instance YDown.instFrame: Frame YDown := { up = -1, unit = rfl }

   def Vector.turnRight [auto frame: Frame f] (v: Vector f): Vector f :=
     { x = frame.up * v.y, y = 0 - frame.up * v.x }
   ```

   One formula turns clockwise *as drawn* in both frames: with y up, (x, y) goes to (y, -x);
   with y down, to (-y, x). Tests: north turned right is east in both frames, and north is
   y = -1 with y down.
2. **The lemmas are proved once, for both frames.** Both theorems check for any frame `f`:

   ```stitchwort
   theorem turnRightVector [auto frame: Frame f] (heading: Heading):
       (heading.vector: Vector f).turnRight = heading.turnRight.vector :=
     match heading with
       | North => Vector.ext _ _ (ring [frame.unit]) (ring)
       | East => Vector.ext _ _ (omega) (omega)
       | South => Vector.ext _ _ (ring [-frame.unit]) (ring)
       | West => Vector.ext _ _ (omega) (omega)

   theorem turnRightFour [auto frame: Frame f] (v: Vector f): v.turnRight.turnRight.turnRight.turnRight = v :=
     Vector.ext v.turnRight.turnRight.turnRight.turnRight v
       (ring [(frame.up * frame.up + 1) * v.x * frame.unit]) (ring [(frame.up * frame.up + 1) * v.y * frame.unit])
   ```

   The frame law `up * up = 1` is all the proofs need. (`turnRightFour` with `_ _` for the
   records failed: `ring` saw unsolved holes. Naming the records fixed it; a small message
   gap, not a design problem.)
3. **Mixing frames is caught.** `v.plus w` with `v: Vector YUp` and `w: Vector YDown` is
   `E-TYPE-MISMATCH`, "expected `Vector YUp`, but this has type `Vector YDown`". Turning a
   `Vector Unoriented` is `E-INSTANCE-NONE`, "no `Frame` instance for `Unoriented`".
4. **2020 day 12 on top of it runs.** `Ship { location: Vector YUp, facing: Heading }` and
   `WaypointShip`, with `moved`, `plus`, `times`, `turnRight` and `manhattan` from the
   library, give the example's 25 and 286. 2021 day 17's probe as two `Vector YUp`s and a
   `Box YUp` target, and 2024 day 13's machine as three `Vector Unoriented`s, check too.
5. **A coordinate-generic point is possible, but buys little.** `type Pt (c: Type) = { x: c,
   y: c }` with `plus` over std's `Add` checks, and so does a commutativity lemma through
   `add.comm`. But std has `Add` and `Mul` only, no subtraction or order between them
   [checked: `crates/elab/src/std/core/AddMul.sw`], so `minus`, `manhattan` and `step` can't
   be written once; and `omega` doesn't work on an unknown `c`.
6. **A small finding.** A type with a constructor of its own name (`type YUp = | YUp`) makes
   every use of `YUp` ambiguous (`E-AMBIGUOUS`, "`YUp` could mean `YUp` or `YUp.YUp`"); the
   frame types need constructors with other names.

## 4. How others do it

**Keeping coordinate spaces apart by a type tag.** Rust's `euclid` tags every point and
vector with a unit, `Point2D<T, U>`, "to prevent mixing values from different spaces": "it
should not be legal to translate a screen-space position by a world-space vector" [R1]. It
has `UnknownUnit` for code that doesn't care, and `cast_unit` to change the tag on purpose
[R2]. Elm's `elm-geometry` goes furthest: `Point2d units coordinates` has two tags, and its
README contrasts a point "defined in Y-up coordinates (from the lower-left corner of an SVG
drawing)" with one "defined in Y-down coordinates from the top left corner of the screen";
the compiler stops you mixing them [R3]. This is the design of [§3](#3-what-we-ran), with the
frame as the tag.

**Points and vectors (the affine split).** A *point* is a place; a *vector* is a step. You
can add a step to a place, or subtract two places to get a step, but adding two places means
nothing. `euclid` enforces it: `Point2D + Vector2D` is a point, `Point2D - Point2D` is a
vector, and there is no `Point2D + Point2D` [R2]. Haskell's `linear` has `Point f a`, "a
handy wrapper to help distinguish points from vectors at the type level", with `.-.` (two
points to their difference) and `.+^` (a point plus a step), and laws such as `a .+^ (b .-.
a) = b` [R4]. Mathlib's `AddTorsor` states the same laws in general (`(p₁ -ᵥ p₂) +ᵥ p₂ = p₁`)
[R5]. Matt's Lean 2024 utilities have separate `Point` and `Vec` (both `Int`), with
`Point.vectorTo` and `Point.add` [checked: `~/repos/mdr/aoc/2024/Aoc2024/Utils.lean:222`].

**One type for everything.** Most AoC code doesn't split them. `glam` has `Vec2`, `IVec2`
(`i32`) and `UVec2` (`u32`), named by number type, and no separate point type [R6]. Peter
Norvig's AoC utilities say it outright: `Point = tuple[int, ...]` and `Vector = Point`, "(1,
0) can be a point, or can be a direction" [R7]. Todd Ginsberg's Kotlin `Point2D(x: Int, y:
Int)` is both too, with `NORTH`, `SOUTH`, `EAST`, `WEST` as constant points to add [R8].
Matt's Scala `Point(x: Long, y: Long)` adds a `Direction` or another `Point` [checked:
`~/repos/mdr/aoc/2015-2021-scala/src/main/scala/aoc/util/Point.scala`].

**Nat against Int.** `glam` keeps unsigned and signed vectors as separate types (`UVec2`,
`IVec2`) [R6]. Mathlib indexes a matrix by any types, `Matrix m n α = m → n → α`,
conventionally `Fin m` and `Fin n`, so a cell index can't even go past the edge [R9]; 2025
day 7 does this with `Fin width`. No library above has one point type generic over its
number type that is also used for grid indices.

**Up and down.** Three approaches:

- *Pick one convention and name directions by it.* Norvig's `North = (0, -1)`, y going down
  [R7]; Ginsberg's `NORTH = Point2D(0, -1)`, y going down [R8]; Matt's Scala
  `North extends Direction(y = 1)`, y going up [checked: `Direction.scala`]. Each is fine
  inside its own code; the three disagree with each other.
- *Complex numbers* (Python): a place is `x + yj` and a turn is a multiplication by `1j` or
  `-1j`. Whether `1j` is a left or a right turn depends on the y convention, and people trip
  on it: in one 2020 day 12 thread, one solution sets north to `1` and east to `1j` so that
  `* 1j` turns clockwise, and another points out that with y up the same multiplication
  turns anticlockwise; a 2018 day 13 solution with y going down notes that a left turn is
  `* -1j` [R10].
- *Tag the frame in the type*: `euclid` and `elm-geometry` [R1, R3].

`linear`'s `perp` is "the counter-clockwise perpendicular vector": with y up, anticlockwise
is a left turn, and with y down the same formula turns right as drawn [R11, inferred]. This is
the trap the frame parameter removes: `turnRight` means "clockwise as drawn" in both.

## 5. Options

### (a) Nat against Int

- **A1. Separate types** (as now: `Position` Nat, `Offset` Int). Each has the operations
  its world allows: a Nat step off the edge is `Option`, an Int step is total. Proofs run on
  concrete numbers, so `omega` and `cases` work.
- **A2. One type with a number parameter**, `Point2 c`. Only `plus` and `times` can be
  shared (std's `Add`, `Mul`); `minus`, `step`, `manhattan` and `within` differ between Nat
  and Int, and generic lemmas lose `omega` ([§3](#3-what-we-ran) item 5). A project
  interface `Coordinate` with subtraction and laws could be written, but every lemma would
  then reason through the interface's laws rather than by `omega`.
- **A3. Int everywhere.** Simplest; drops the "never negative" guarantee that makes grid
  steps `Option` and grid indices safe, which Matt wants to keep.

Conversions between the worlds are total one way and `Option` the other way, as `Offset.sw`
already does: `Position.minus` gives an `Offset`, `Position.offset` gives `Option Position`,
with `offsetMinus` and `minusOffset` as the round trip [checked: `Proofs/Offset.sw:92`].

**Recommendation: A1.**

### (b) Which way y goes

- **B1. Conventions in the field names, no parameter.** `rows`/`columns` mean down/right;
  a new `Int` type takes `east`/`north` (y up). No type has an ambiguous `y`, but 2021 day 17
  ("the probe's x position", "y position") and 2024 day 13 ("X", "Y") would speak in compass
  words the puzzle doesn't use, and a y-down `Int` `x,y` puzzle (2024 d14's velocities) gets
  neither name.
- **B2. A frame type parameter on the `x,y` type** ([§3](#3-what-we-ran)): `Vector YUp`,
  `Vector YDown`, `Vector Unoriented`. The puzzle's own words (`x`, `y`) stay; the frame is
  stated once, in the day's types; lemmas are proved once.
- **B3. A frame value** passed to each turn (`v.turnRight (frame := yUp)`). The same lemmas,
  but every call passes it and nothing stops two frames meeting.
- **B4. One convention for the library** (y up, or y down). What most AoC helpers do
  ([§4](#4-how-others-do-it)); it "overcommits", which is what Matt wants to avoid, and
  Common already has `Point` with y down.

Directions in every option: `Direction` (up, right, down, left) and `Heading` (north, east,
south, west) are words about the *picture*, so neither needs a frame. Turning a direction
is the same in every frame. Only `Heading.vector`, `Vector.step` and `Vector.turnRight` ask
the frame; `Direction.offset` (rows and columns) never needs to.

**Recommendation: B2 on the `x,y` Int type only**; rows and columns stay as they are (B1's
half that already works).

### (c) Places against steps

- **C1. Split only where the numbers differ.** A Nat place (`Position`, `Point`) and an Int
  step (`Offset`, `Vector`): the Nat/Int line already *is* the place/step line. In an Int
  plane, one type serves both, as `Offset` already does for 2024 day 15's board with no edge.
- **C2. Split everywhere** (`euclid`, `linear`, Matt's Lean): an Int `Place f` beside
  `Vector f`. It would catch adding two places; in the corpus, 2020 day 12 (ship and
  waypoint) is the one day that holds both kinds of `Int` value, and its proofs never
  confused them. It doubles the types, conversions and lemmas.

**Recommendation: C1.** The split pays where Nat and Int differ, and there it's free.

### (d) Grids

`Grid a` (rows as lists, with `lookup` through a `Map` built once) stays the parsed, dense
view. Sparse views are already std's: `Map Position a` (2024 d12) and `Set Position` (2024
d6, d16, d18, d20); `Position` gets its order from the compiler, since a record derives `Ord`
field by field [checked: `docs/syntax.md`, Interfaces, "A declared data type or record gets
one derived"]. A sheet's `Point` converts to a `Position` (`Point.toPosition`, as now); with
frames, only a `YDown` vector converts to grid steps, so a y-up plane can't be drawn upside
down by accident. Five days carry a height and a width side by side; a small `Size { height,
width }` with `contains`, `positions` and `graph` (Common's `within`, `positions` and
`boxGraph` today) gives them one name.

### (e) Lemmas, and reuse across variants

- Frame-generic lemmas ([§3](#3-what-we-ran)): one statement for every frame, proved with
  the frame law.
- Nat/Int lemmas: the round trips (`offsetMinus`, `minusOffset`, `offsetPlus`, as
  `Proofs/Offset.sw` has for `Position`), stated for each pair; they are a line or two of
  `omega` each.
- Links between the worlds: `Heading.toDirection`, and `(heading.vector: Vector YDown) =
  heading.toDirection.offset.toVector`, so a day can move between a grid and a plane
  without re-proving steps.
- Turning by a number of quarter turns needs `Nat.iterate` with a period (2020 day 12's
  `iterateMod`, 12 lines); that belongs in std (SW-1486).

### (f) Names, and how a day sits on top

Per CLAUDE.md, a day still wraps these in its own records (`Ship`, `Probe`, `Machine`); the
library gives the fields' types and the operations. Names a reader can't misread:
`Position.row`, `Offset.rows`, `Point.x` (on a sheet, y down by its doc), `Vector YUp`'s `y`
(up, by its type). Two names clash today and should go: 2024 day 13's `Offset { x, y }` (it
becomes a `Vector Unoriented`) and 2025 day 8's 3D `Point` (rename to `Box3`, or
`JunctionBox`, in the day).

## 6. The recommendation

### Types

| | Nat: a place that can't go negative | Int: a step, or a place with no edge |
|---|---|---|
| **rows and columns** (y down, by name) | `Position { row, column }` (as now) | `Offset { rows, columns }` (as now) |
| **x and y** | `Point { x, y }` (as now; a printed sheet, y down) | `Vector f { x, y }`, with `f` = `YUp`, `YDown` or `Unoriented` (new) |

Directions: `Direction` (`Up`, `Right`, `Down`, `Left`, as now) and `Heading` (`North`,
`East`, `South`, `West`, new; 2024 d16's moves here), each with `turnRight`, `turnLeft`,
`opposite` and `turned quarters`; `Heading.toDirection` and `Direction.toHeading` convert
(north is up). Eight directions: `compass: List Offset` (SW-1475).

Shapes: `Size { height, width }` for grids from the top-left corner; `Box f { low, high }`
(corners included) for planes, with `contains`, and `top` and `bottom` that ask the frame
(with y up the top is the largest y); `Line` (as now).

### Modules

- `Common/Grid.sw`, `Offset.sw`, `GridGraph.sw` (as now), plus: `compass`, `Grid.ray` and
  its first-cell lemma (SW-1475), a cheaper `around` proved equal to today's (SW-1474),
  `Position.manhattan` and `diamond` (from 2024 d20), `Position.diagonal` (from 2024 d12),
  `Size`.
- `Common/Plane.sw` (new): `Frame`, `YUp`, `YDown`, `Unoriented`, `Vector f` (`zero`,
  `plus`, `minus`, `negate`, `times`, `manhattan`, `turnRight`, `turnLeft`, `turned
  quarters`, `step heading`, `moved heading distance`), `Heading`, `Box f`, and the
  conversions `Point.toVector: Vector YDown`, `Vector.toPoint: Option Point`,
  `Offset.toVector: Vector YDown`, `Vector.toOffset`.
- `Common/Orientation.sw` (stage 3, SW-1587): `rotate`, `flip`, `orientations`, `edges`,
  `crop` on rows, with std's transpose lemmas (SW-1588).

### Lemmas (Plane)

`turnRightFour`, `turnLeftRight`, `turnRightLeft`, `turnedMod` (quarters past 4 wrap),
`turnRightVector` and `turnLeftVector` (turning a heading turns its step), `manhattanTurn`
(a turn keeps the length), `manhattanTriangle`, `plusComm`, `plusAssoc`, `minusPlus`,
`toVectorToPoint` and `toPointToVector` (the round trip), `headingVectorDown` (a `YDown`
step is the grid step), `boxContains` (`contains` as inequalities). All frame-generic ones
use `frame.unit`, as in [§3](#3-what-we-ran).

## 7. Before and after

Sketches; the first three were checked in scratch files ([§3](#3-what-we-ran) item 4). The
day 11 one uses names that don't exist yet.

**2020 day 12.** Before: `Location { east, north }` with `moved`, `plus`, `times`,
`rotated`, `manhattan`, `Heading` with `clockwise` and `turned` (about 35 lines), and
Turns.sw (81 lines of proofs). After:

```stitchwort
import Aoc.Common (Heading, Vector, YUp)

--| Part 1's ship: where it is from its start, and which way it faces.
type Ship = { location: Vector YUp, facing: Heading }

def Ship.follow (ship: Ship) (instruction: Instruction): Ship :=
  match instruction.action with
    | Move heading => { ship | location = ship.location.moved heading instruction.value }
    | Turn side => { ship | facing = ship.facing.turned (clockwiseQuarters side instruction.value) }
    | Forward => { ship | location = ship.location.moved ship.facing instruction.value }

--| Part 2's: the waypoint is a step from the ship.
type WaypointShip = { location: Vector YUp, waypoint: Vector YUp }
-- Turn side => { ship | waypoint = ship.waypoint.turned (clockwiseQuarters side instruction.value) }
```

The day keeps `Side`, `Action`, the parser and `clockwiseQuarters`; Turns.sw becomes calls
to `turnedMod` and `turnRightVector`. The spec can say "north" and mean the puzzle's north.

**2021 day 17.** Before: `Target { left, right, bottom, top }`, `Probe { x, y, dx, dy }`.
After:

```stitchwort
type Probe = { position: Vector YUp, velocity: Vector YUp }

def Probe.step (probe: Probe): Probe := {
  position = probe.position.plus probe.velocity,
  velocity = { x = probe.velocity.x - probe.velocity.x.sign, y = probe.velocity.y - 1 }
}

def Probe.fallen (probe: Probe) (target: Box YUp): Bool := probe.position.y < target.bottom ∧ probe.velocity.y < 0
```

Gravity is `y - 1` because the type says y goes up; `target.bottom` is the lowest y for the
same reason. The day's proofs are `omega` over the fields and should move with renames only
[inferred].

**2024 day 13.** Before: a local `Offset { x, y }` that hides Common's. After:

```stitchwort
type Machine = { buttonA: Vector Unoriented, buttonB: Vector Unoriented, prize: Vector Unoriented }

def Machine.wins (machine: Machine) (aPresses: Nat) (bPresses: Nat): Bool :=
  machine.buttonA.times aPresses.toInt |> .plus (machine.buttonB.times bPresses.toInt) |> (== machine.prize)
```

The claw has no up, and the type says so: nothing in the day can turn or step by a heading.

**2020 day 11, part 2.** Before: `compass` (10 lines) and `firstSeat` (a ray walked by hand),
with 70 generic lines in Sight.sw. After (SW-1475's names):

```stitchwort
def Layout.sightRule (layout: Layout): Rule := {
  inView = find from => compass.filterMap (direction => layout.grid.ray from direction |> .find (seen => find seen != Some Floor)),
  tolerance = 5
}
```

with SW-1475's lemma (the first cell along `grid.ray from offset` that passes a test is the
spec's first seat in sight) doing Sight.sw's generic part, and no `reach` to pass.

**2021 day 5 stays as it is.** It uses `Point` and `Line` on a sheet, and up never comes into
it. The library shouldn't make it write a frame, and in this design it doesn't.

## 8. Staged plan

1. **Plane (SW-1484, rescoped).** `Common/Plane.sw` and `Proofs/Plane.sw` as in
   [§6](#6-the-recommendation); move 2020 d12, 2021 d17 and 2024 d13 onto it; 2024 d16's
   `Heading` moves to Common. Sonnet, about 90 minutes, as SW-1484 was estimated. Needs
   `Nat.iterate` with a period (SW-1486) or carries it in Plane for now.
2. **Grid extras.** SW-1475 (`compass`, `Grid.ray`, the first-cell lemma; 2020 d11 moves),
   SW-1474 (a cheaper `around`), `Position.manhattan`, `diamond`, `diagonal`, `Size` (2021
   d15, 2024 d6, d8, d14, d18 move). 2024 d21 imports Common's `Position` and `Direction`
   instead of its own. SW-1482 (2021 d11 onto `countAround`) is independent and can go any
   time.
3. **Orientations.** SW-1588 (std transpose lemmas) then SW-1587 (`Orientation.sw`); 2020 d20
   moves, and its places become a `Set Position`.
4. **Close SW-1592** after a check: `Position` already gets `Ord` from the compiler (2024
   d6's `Set Position` and d12's `Map Position Char` check), and std has an order for pairs
   ([§5 (d)](#d-grids)); 2020 day 20's note (item 5) was wrong about both. A lane should
   confirm with a three-line scratch file, and then move day 20 to `Set Position` in stage 3.
   Common's `Point.instOrd` (`Point.sw:20`) can then probably go too, since the derived order
   is the same (x, then y).

Not planned: a 3D type (two days, one Nat, one `List Int`; let them be), a generic number
type (A2), an Int `Place` type (C2), and grids backed by an array (a runtime question, in
2020 day 11's note).

## 9. Decisions

- **Q1. Nat and Int stay separate types** (A1): `Position` and `Point` for places, `Offset`
  and `Vector` for steps, no type generic over its number. [rec: yes]
- **Q2. The frame of an `x,y` Int type is a type parameter** (B2): `Vector YUp`,
  `Vector YDown`, `Vector Unoriented`, with turns and steps proved once for every frame.
  The fallback is B1 (a y-up type with `east`/`north` fields). [rec: yes, B2]
- **Q3. The new type's name is `Vector`.** Others: `Coords f`, `Plane f`, D2456's `Point`
  (taken by the Nat sheet type). It isn't std's `Vec` (sized lists), but is close to it.
  [rec: `Vector`]
- **Q4. No separate Int place type** (C1): `Vector f` is a place in the plane and a step
  across it, as `Offset` is on a board with no edge. [rec: yes]
- **Q5. `Direction` (up, right, down, left) and `Heading` (north, east, south, west) are
  both kept**, as picture words with no frame, converting into each other; a day uses the
  puzzle's words. This answers 2020 friction Q4. [rec: yes]
- **Q6. Common's `Point` keeps y going down, with no frame parameter**, because every Nat
  `x,y` puzzle in the corpus is a sheet printed from the top; it converts to `Vector YDown`.
  If a y-up Nat puzzle comes (a falling-rocks tower, say), reopen this. [rec: yes]
- **Q7. `Offset` (rows, columns) stays beside `Vector YDown` (x, y)**, with conversions,
  rather than grids switching to `x`/`y`. [rec: yes]
- **Q8. A `Size { height, width }` record** for grids from the top-left corner, for the five
  days that carry the pair. [rec: yes, in stage 2]
- **Q9. Stages as in [§8](#8-staged-plan)**, SW-1484 rescoped to stage 1 and started next on
  Sonnet. [rec: yes]

## 10. Evidence still to collect

- **Cost of the dictionary at run time.** `turnRight` multiplies by `frame.up`; check that
  2020 day 12's run time doesn't change (0.35 s user today).
- **The counterexample search and `stitchwort doc` on `Vector YUp`**: that the search makes
  values of a record with a phantom parameter, and that `doc` shows the frame.
- **The proofs that move.** Stage 1 should report how many of 2020 day 12's 81 Turns.sw
  lines and 2021 day 17's `omega` proofs survive, as the measure of whether the library pays.
- **More years.** The plane's case rests on 3 of 28 days. Matt's other years (2015 to 2023
  in `~/repos/mdr/aoc`, in Scala, Idris and Lean) would show how often y goes up and whether
  boards with no edge (Int, y down) are common enough to want `Vector YDown` rather than
  `Offset` [unverified: from memory, several 2022 and 2023 days are like that].
- **SW-1592**: the scratch check in [§8](#8-staged-plan) item 4.

## Sources

- [R1] euclid 0.22.14, crate docs: https://docs.rs/euclid/latest/euclid/
- [R2] euclid, `Point2D` (its `Add<Vector2D>`, `Sub` giving `Vector2D`, `to_vector`,
  `cast_unit`): https://docs.rs/euclid/latest/euclid/struct.Point2D.html
- [R3] elm-geometry 4.0.0, README (units and coordinate systems, Y-up against Y-down):
  https://github.com/ianmackenzie/elm-geometry (README.md)
- [R4] linear 1.23.3, `Linear.Affine` (`Affine`, `.-.`, `.+^`, `Point`):
  https://hackage.haskell.org/package/linear/docs/Linear-Affine.html
- [R5] Mathlib, `AddTorsor` (`vsub_vadd'`, `vadd_vsub'`):
  https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/AddTorsor/Defs.html
- [R6] glam 0.34.2, crate docs (`Vec2`, `IVec2`, `UVec2`): https://docs.rs/glam/latest/glam/
- [R7] Peter Norvig, pytudes, AdventUtils.ipynb (`Point`, `Vector = Point`, `directions4`,
  `taxi_distance`, `Grid`):
  https://github.com/norvig/pytudes/blob/main/ipynb/AdventUtils.ipynb
- [R8] Todd Ginsberg, advent-2023-kotlin, `Point2D.kt`:
  https://github.com/tginsberg/advent-2023-kotlin/blob/main/src/main/kotlin/com/ginsberg/advent2023/Point2D.kt
- [R9] Mathlib, `Matrix` (`Matrix m n α = (m → n → α)`):
  https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Matrix/Defs.html
- [R10] r/adventofcode solution threads on complex numbers for turning: 2020 day 12
  (https://www.reddit.com/r/adventofcode/comments/kbj5me/2020_day_12_solutions/), 2018
  day 13 (https://www.reddit.com/r/adventofcode/comments/a5qd71/2018_day_13_solutions/),
  2024 day 6 (https://www.reddit.com/r/adventofcode/comments/1h7tovg/2024_day_6_solutions/);
  read through mirrors.
- [R11] linear 1.23.3, `Linear.V2` (`perp`, "the counter-clockwise perpendicular vector"):
  https://hackage.haskell.org/package/linear/docs/Linear-V2.html
- Matt's own AoC code (`~/repos/mdr/aoc`): Scala `aoc/util/Point.scala`, `Direction.scala`,
  `Grid.scala` (2015 to 2021); Lean `2024/Aoc2024/Utils.lean`.
