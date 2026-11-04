# SW-1283: AoC solutions, candidates for domain types

Survey date 4 Nov 2026. Read-only. Method: for all 56 days I read the program's
`def`/`type` signatures and the Spec's signatures; I read the program body in
full only for 2021/03, 04, 05, 11, 12, 2024/09, 2025/08 (the ones where a sketch
needed exact code). Proof counts are `grep` approximations ("lines": Spec+Proofs
lines that mention the raw type; "thms": `theorem` count in that day's Proofs/).
They say how big a refactor lane is, not exactly how many statements change.
Sketches are indicative; none was type-checked.

All paths are under `/Users/matt/repos/mdr/stitchwort/aoc/src/Aoc/`.

## Summary

The solutions are already in better shape than the ticket's framing suggests.
About 30 of 56 days already have the puzzle's nouns as records or variants
(Entry, Passport, Slope, Command, Segment/Pattern/Wiring, Dot/Fold, Packet,
Target/Probe, Number/Leaf, Guard/Lab, Equation, Machine, Robot/Space, Wire/Gate/
Device, Dial/Turn, Database, Manifold, ...). What is left is concentrated in:

- **Raw lists of lists / tuples of Text** where a noun hides: 2021/11, 2021/12.
- **Transparent aliases** (`type Bits = List Bool`, `def Computer: Type := Text`,
  `def Pattern: Type := List Stripe`) that name the noun but do not give it a
  type of its own.
- **Spec and proof statements** that go back to the raw type even where the
  program has a record (2024/18 `size`+`bytes`, 2024/05 `pages`, 2024/12
  `List Position` regions, 2021/12 `List Text` paths).
- **Duplicated shapes across days** that belong in `Aoc.Common` (bits, x/y
  points, undirected edges, grid wrappers, direction types).

Counts: 6 high, 11 medium, 13 low candidates (30 in all); 5 shared shapes for
Common; 26 days with nothing worth doing (listed at the end).

One decision for Matt before picking (a D question): **alias or record?**
Aliases (`def Bank: Type := List Battery`) already support dot-notation methods
(2025/03 does `.maxJoltage` on them) and cost almost no proof churn, but they
give no type safety and statements can still be written on the raw type. A
record or one-field wrapper is the real fix but changes every statement that
mentions the type. My suggestion: records for nouns that carry methods the
proofs talk about; leave an alias where the raw list really is the whole story.
Day 5's `Pass = { bits: List Bool }` is the record route.

### Top 10, ranked

1. **2021/12 Cave, Passage, Path.** `Text`, `(Text, Text)`, `List Text` everywhere;
   `isBig`, `neighbours`, `visits` become methods. 61 thms, ~113 lines. High value, large lane.
2. **2021/11 Octopus grid.** `List (List Nat)` and `List (List Bool)` threaded by
   hand next to Common's `Grid`. 44 thms, ~63 lines. High value, large lane.
3. **Shared `Bits`** (2021/03 first, then 2021/16, 2024/24; 2020/05 is the model).
   `Nat.fromBits`, `mostCommon`, `afterBit` become methods. 19 thms for 2021/03.
4. **2024/12 Region.** `List Position` with `area`/`perimeter`/`sides` as methods
   (Spec already has these as free functions on the same list). 86 thms; costly but
   the spec statements get much clearer.
5. **Shared `Point {x, y}`** (2021/05 tuple `Point`, 2021/13 `Dot`, 2025/09 `Tile`)
   plus a `Segment`. Mostly renaming; 2021/05 gains most.
6. **2024/09 Block / DiskMap.** `List (Option Nat)` is a disk of blocks; `List Nat`
   is the disk map. 31 thms, ~27 lines.
7. **Grid-wrapper normalisation** (2021/09, 2021/15, 2024/10, 2024/04). Each
   re-declares `{ rows }` and converts to/from Common `Grid`. Medium churn.
8. **2021/04 Board.** `type Board = List (List Nat)` to a record with `lines`,
   `unmarkedSum`. Only ~15 lines mention it. Cheap.
9. **2024/23 Computer / Connection.** `Text` alias and `(Computer, Computer)`.
   `startsWithT` method replaces `mightBeChiefs`/`hasT` in program and spec. 44 thms.
10. **2025/09 Rectangle / Edge** for `(Tile, Tile)`. Few spec lines (~13); cheap.

Cheapest wins, if Matt wants quick lanes: 2021/04, 2025/09, 2024/13 (rename),
2021/14, 2024/19.

---

## 2020

### 2020/01: trivial
`List Nat` entries, `(Nat, Nat)` / `(Nat, Nat, Nat)` results of
`findPair`/`findTriple` (Day01.sw:36,47). The entries are plain numbers and the
pair is immediately multiplied. Skip.

### 2020/05: in progress (SW-1282)
`Pass = { bits: List Bool }`, `pass.seatId`. The model for the rest; its
sibling candidates are the shared `Bits` below.

Days 02, 03, 04 are in good shape (Entry with `validByCount`; Square/Slope/Grid;
Key/Field/Passport with `Passport.has`).

---

## 2021

### 2021/03 Bits (HIGH, shared Bits)
- Raw type: `type Bits = List Bool` (Day03.sw:33), and `List Bool` for a column
  of bits (`mostCommon`, `rating (choose: List Bool → Bool)`, Day03.sw:48,65).
- Noun: a diagnostic number (a row of the report), and a column of it.
- Flows: `parseReport`, `solvePart1`, `afterBit`, `rating`, `solvePart2`;
  Spec `width`, `howMany`, `mostCommonAt`, `gammaRate`, `keep`, `findRating`,
  `oxygenGeneratorRating`... (Spec.sw:31-78); Proofs.sw:13-84 (19 thms, ~47 lines).
- Proposal: `type Number = { bits: List Bool }` (or Common `Bits`, see Shared)
  with `Number.value : Nat` (= `Nat.fromBits`), `Number.width`, `Number.afterBit`;
  `Report = { numbers: List Number }` with `Report.width`, `Report.column i`,
  `Report.gamma`, `Report.epsilon`.
- Sketch:
  ```
  -- before
  def solvePart1 (numbers: List Bits): Nat :=
    let gamma: Bits := numbers.transpose |> .map mostCommon
    Nat.fromBits gamma * (Nat.pow 2 gamma.length - 1 - Nat.fromBits gamma)
  -- after
  def Report.gamma (report: Report): Number := { bits = report.columns.map mostCommon }
  def solvePart1 (report: Report): Nat := report.gamma.value * report.gamma.complement.value
  ```
- Benefit: `gammaRate`/`epsilonRate` read as "gamma/epsilon of the report";
  `Nat.fromBits gamma` noise goes; `epsilonComplement` becomes a statement about
  `Number.complement`. Cost: all 19 theorems touch `Bits`; moderate rewrite, but
  mechanical (they unwrap `.bits` at the edge). Score: **high**.

### 2021/04 Board (MEDIUM)
- Raw: `type Board = List (List Nat)` (Day04.sw:31); `draws: List Nat`.
- Noun: bingo board; the draws.
- Flows: `isFiveByFive`, `Board.lines`, `winningTurn`, `score` (Day04.sw:60,67);
  Spec `wins`, `finalScore`, `play`; Proofs: 13 thms, ~15 lines mention `Board`.
- Proposal: `type Board = { rows: List (List Nat) }`; methods `Board.lines`,
  `Board.numbers`, `Board.isFiveByFive`, `Board.unmarkedSum (drawn)`,
  `Board.winsAfter (drawn)`. Optionally `Draws` wrapper with `Draws.turnOf number`
  (replaces `draws.indexOf`).
- Sketch:
  ```
  -- before
  def winningTurn (draws: List Nat) (board: Board): Nat := board.lines |> .map (line => ... draws.indexOf number) ...
  -- after
  def Board.winningTurn (board: Board) (draws: Draws): Nat := board.lines |> .map draws.lastTurnOf |> .foldLeft draws.length Nat.min
  ```
- Benefit: readability moderate (it is already named); gives `score` and
  `winningTurn` a home. Cost: low (13 thms, most take `Board` opaquely).
  Score: **medium** (cheap).

### 2021/05 Point and Line (HIGH as part of shared Point)
- Raw: `type Point = (Nat, Nat)` (Day05.sw:30); `Line = { x1, y1, x2, y2 }` (:33).
- Noun: a grid point; a vent line from one point to another.
- Flows: `Line.points`, `overlaps` (Day05.sw:75-84); Spec `covers`, `between`,
  `coveredBy`, `overlap`, Part1/2Answer; Proofs: 37 thms, ~52 lines mention x1/y1/Point.
- Proposal: Common `Point = { x: Nat, y: Nat }` and `Line = { from: Point, to: Point }`
  (or `Segment`); methods `Segment.isStraight`, `isDiagonal`, `points`, `covers`;
  parser still reads `x1,y1 -> x2,y2`.
- Sketch:
  ```
  -- before
  def Line.isStraight (line: Line): Bool := line.x1 == line.x2 ∨ line.y1 == line.y2
  -- after
  def Segment.isStraight (segment: Segment): Bool := segment.from.x == segment.to.x ∨ segment.from.y == segment.to.y
  ```
- Benefit: the tuple `Point` stops being a bare pair; `x1/y1/x2/y2` fields become
  two points, so `covers segment point` and `segment.points` read naturally and
  2025/09's `(Tile, Tile)` can share `Segment`. Cost: 37 thms, 52 lines (the
  field accesses `line.x1` change throughout Parse.sw/Proofs.sw). Score: **medium-high**.

### 2021/06 Fish (LOW)
`List Nat` timers (Day06.sw:30,74); `Counts` is already the domain type. Spec
`nextTimer`/`nextDay` on `List Nat`. A `Fish = { timer: Nat }` is a thin
wrapper. 23 thms. Score: **low**.

### 2021/07 Crabs (LOW)
`List Nat` crab positions (Day07.sw:31,40,51). A position is a number, the list
is the puzzle input. A `Crabs` wrapper would hold `leftmost`/`rightmost`/`fuelAt`
(the helpers at Day07.sw:46-51 are free functions on `List Nat`). ~48 lines
mention `crabs`. Score: **low**.

### 2021/09 HeightMap (see Shared, grid wrappers) MEDIUM
`type HeightMap = { rows: List (List (Fin 10)) }` (Day09.sw:30ish) is a
re-declared `Grid` without `nonEmpty`; `HeightMap.cells`/`heightAt` call the
Common list functions directly on `rows`. Contrast 2021/15 `Cave` which has both
`Cave.ofGrid` and `Cave.grid` conversions. Also 2021/09 and 2025/08 both define
a "three largest, multiplied" helper (`largestThreeProduct`, `threeLargestProduct`).

### 2021/10 Line of tokens (LOW)
`List (List Token)` (Day10.sw:51; used in Spec as `List (List Token)` for
`Part1Answer`/`Part2Answer`). Bracket and Token are already types. A
`Line = { tokens }` with `corruptionScore`/`autocompleteScore` as methods is
nice but small. Score: **low**.

### 2021/11 Octopus grid (HIGH)
- Raw: `List (List Nat)` for energy levels, `List (List Bool)` for who flashed
  (Day11.sw:25ish; `flashedAt`, `energy`, `flashRound`, `cascade`, `flashers`,
  `step`, `zeros`, `flashesIn`, `firstSync`).
- Noun: the cavern of octopuses; a step.
- Flows: all program defs above; Spec uses `List (List Nat)` plus `Position → Bool`
  for flashed (`flashingNeighbours`, `energyIn`, `Closed`, `Flashers`, `after`,
  `Run`); Proofs: 6 files, 44 thms, ~63 lines.
- Proposal: use Common `Grid`: `type Cavern = { grid: Grid Nat }` (octopus energy
  as `Nat`), `Cavern.step`, `Cavern.flashes`, `Cavern.allFlashed`; flashed set as
  `Set Position` or `Grid Bool`. `parseLevels` returns `Cavern` instead of
  `numbers (parseGrid ...)` which converts `Fin 10` to `Nat` by hand.
- Sketch:
  ```
  -- before
  def step (levels: List (List Nat)): List (List Nat) :=
    let flashed := flashers levels
    mapCells levels (at level => if flashedAt flashed at then 0 else energy flashed at level)
  -- after
  def Cavern.step (cavern: Cavern): Cavern :=
    let flashed := cavern.flashers
    cavern.map (at level => if flashed.contains at then 0 else cavern.energy flashed at level)
  ```
- Benefit: removes the `List (List …)` type from ~60 lines, uses `Grid` methods
  (`Grid.map`, `Grid.at`, `Grid.cells`). Cost: high (44 thms; Around.sw,
  Cascade.sw, Rounds.sw, Step.sw reason about `cellAt` on raw rows). Needs a
  proof lane; if Grid is used the proofs may get easier (Grid lemmas exist in
  `Common/Proofs/Grid*.sw`). Score: **high** value, high cost.

### 2021/12 Cave, Passage, Path (HIGH)
- Raw: `Text` for a cave, `(Text, Text)` for a passage, `List (Text, Text)` for the
  map, `List Text` for a path, `List (Text, List Text)` for the neighbour table
  (Day12.sw:41, 67, 120).
- Noun: cave (big/small/start/end), passage, route.
- Flows: Day12.sw defs `isBig`, `passage`, `checkPassages`, `caves`,
  `neighboursOf`, `neighbourTable`, `smallCaves`, `step`, `routesFrom`, `paths`;
  Spec.sw:11-28 `connected`, `followsPassages`, `startToEnd`, `visits`, `SmallOnce`,
  `Part1Path`, `OneSmallTwice`, `Part2Path`; Proofs: 6 files, 61 thms,
  ~113 lines.
- Proposal: `type Cave = { name: Text }` with `Cave.isBig`, `Cave.isSmall`,
  `Cave.isStart`, `Cave.isEnd`; `type Passage = { from: Cave, to: Cave }` with
  `Passage.joinsBig`, `Passage.connects`; `type CaveSystem = { passages: List Passage }`
  with `neighbours`, `caves`, `smallCaves`; `type Route = { caves: List Cave }` with
  `Route.visits`, `Route.startsAtStart`.
- Sketch:
  ```
  -- before
  def step (unvisited: List Text) (spare: Bool) (cave: Text) (other: Text): Step :=
    if other == "end" then Finish else if other == "start" then Blocked
    else if isBig other then (if isBig cave then Blocked else Continue unvisited spare) ...
  -- after
  def step (unvisited: List Cave) (spare: Bool) (cave: Cave) (other: Cave): Step :=
    if other.isEnd then Finish else if other.isStart then Blocked
    else if other.isBig then (if cave.isBig then Blocked else Continue unvisited spare) ...
  ```
- Benefit: magic strings `"start"`/`"end"` and `isBig` become methods; the
  `Part1Path` statements read as "route from start to end that visits each small
  cave once". Cost: every one of 61 thms (string-equality reasoning wraps in
  `Cave`); proof lane is slow. A cheaper partial: a `Cave` alias with methods
  (`def Cave: Type := Text`) gets the vocabulary with zero proof churn.
  Score: **high** (the noun-rich day), do last or as alias first.

### 2021/13 Dot, Fold, Paper (GOOD) with LOW item
Already domain types. `List (List Char)` is the rendered picture
(Day13.sw:111,115,123; Spec `cellAt`, `Shows`); `Picture = { rows }` with
`Picture.show` replacing `showPicture`. ~31 thms. Score: **low**.

### 2021/14 Element pair (MEDIUM-LOW)
- Raw: `(Char, Char)` pair of elements, `Map (Char, Char) Char` rules, `type PairCounts =
  Map (Char, Char) Nat` (Day14.sw:74,78,84,93).
- Noun: an adjacent pair of polymer elements; an insertion rule.
- Flows: `Rule.pair`, `ruleTable`, `becomes`, `stepCounts`; Spec `insertionFor`,
  `between`; Proofs 35 thms (Pairs.sw, Table.sw, Counts.sw). Only ~13 lines
  mention `(Char, Char)` though.
- Proposal: `type Pair = { left: Char, right: Char }` (Rule could then hold
  `pair: Pair, insert: Char`), `Pair.becomes table`. Benefit: modest.
  Cost: Map keys change (needs an `Ord`/`Hashable` instance like `Dot.instOrd`).
  Score: **low-medium**.

### 2021/15 Cave risk map (GOOD, but see grid wrappers)
`Cave` + `RiskMap` are domain types. `Cave.ofGrid`/`Cave.grid` conversions are
the grid-wrapper smell.

### 2021/16 Transmission bits (MEDIUM-LOW)
- Raw: `List Bool` as the transmission and the unread remainder, threaded through
  `readBits`, `splitField`, `readNumber`, `readPackets`, `readPacket` (Day16.sw:81-137);
  Spec `bitsOf`, `encode`, `transmissionBits : … → Option (List Bool)`.
- Noun: the bit stream being decoded.
- Proposal: shared `Bits` with `Bits.take n`, `Bits.toNat`, or a `BitReader`
  (the remainder is always returned as a pair `Option (a, List Bool)`; a reader
  record with `read n`, `readPacket` would replace the manual tuple threading).
  Cost: 66 thms, ~42 lines. Benefit: moderate. Score: **medium**; do after Bits exists.

### 2021/17 Target, Probe, Velocity (GOOD)
Also see Shared (Interval): `Target { left, right, bottom, top }` is two Int ranges.

### 2021/18 Number, Leaf, Explosion (GOOD)
Already domain types.

Days 01, 02, 08 are good (01 `List Nat` depths is the input itself; 02 `Command`
and Spec's `Submarine`; 08 `Segment/Pattern/Wiring/Entry`).

---

## 2024

### 2024/04 Grid (MEDIUM, grid wrappers)
Own `type Grid = { rows: List (List Char) }` (Day04.sw:22) with `parseGrid`
over `List Text`, independent of `Aoc.Common.Grid`; Spec defines its own
`Direction = { down: Step, across: Step }` (Spec.sw:32) with eight directions
including diagonals, separate from Common's four. `letterAt grid r c` (Spec.sw:23)
takes two `Nat`s, not a `Position`. Proposal: use Common `Grid Char`, `Position`,
and a Common `Offset`/8-way direction; `letterAt` becomes `Grid.at`. 40 thms,
~43 lines. The program itself works on rows, never on positions (`countAcross`),
so the program change is small; the spec/proofs carry the cost. Score: **medium**.

### 2024/05 Update pages (LOW)
Program is fine (`Rule`, `Update`, `PrintQueue`). Spec/Proofs go back to raw:
`followsRule (pages: List Nat)`, `printedBefore (x y) : List Nat → Bool`,
`Asymmetric/Total/Transitive (rules) (pages: List Nat)` (Spec). Making them
`Update` methods (`update.followsRule rule`) is cheap. Score: **low**.

### 2024/09 Block and DiskMap (HIGH)
- Raw: `List Nat` disk map (`parseDiskMap`, Day09.sw:29); `List (Option Nat)` for
  blocks, `Some id` file block, `None` free (Day09.sw:33-58; Spec `filesystemChecksum`,
  `lastFile`, `moveLastBlock`, `hasGap`, `compactOneAtATime`, `fileStart`, `freeAt`,
  `moveWholeFile`, `compactWholeFiles`).
- Noun: a block (file `id` or free space), the disk, the disk map.
- Proposal: `type Block = | Free | FileBlock (id: Nat)` with `Block.id : Option Nat`,
  `Block.isFree`; `type Disk = { blocks: List Block }` with `Disk.checksum`,
  `Disk.compact`, `Disk.hasGap`; `type DiskMap = { lengths: List Nat }` with
  `DiskMap.blocks`. Part 2 already has `File`, `Span`, `FreeSpace`, so the
  second half is done.
- Sketch:
  ```
  -- before
  def checksum (blocks: List (Option Nat)): Nat :=
    blocks.withIndex |> .sumBy (pair => pair.snd.map (id => pair.fst * id) |> .getOrElse 0)
  -- after
  def Disk.checksum (disk: Disk): Nat := disk.blocks.withIndex |> .sumBy (((position, block)) => position * block.idOr 0)
  ```
- Benefit: `Option Nat` stops meaning two things (free vs file); spec
  statements on `Option Nat` blocks become readable. Cost: 31 thms, ~27 lines;
  the patterns `[Some id, ..rest]` in `fillFront` become `[FileBlock id, ..rest]`
  (mostly mechanical). Score: **high-medium**.

### 2024/10 TopographicMap (MEDIUM, grid wrappers)
`TopographicMap = { rows: List (List (Option Nat)) }` (Day10.sw:2x) re-declares
Grid; `TopographicMap.ofGrid` drops the nonEmpty proof; `heightAt` calls `cellAt`
on rows. Same fix as 2021/09. Program is otherwise good (trailheads, score,
rating). Score: **medium**, shared.

### 2024/11 Stones (LOW)
`List Nat`, `Map Nat Nat` for stones and their counts (Day11.sw:22-44). A stone
is a number with an engraved value; `Stone.change`, `Stones.blink` would be
methods, but the Spec already works in `List Nat` and the "stone" has no extra
structure. 27 thms. Score: **low**.

### 2024/12 Region (HIGH, medium cost)
- Raw: `List Position` for a region, `List (List Position)` for the regions
  (Day12.sw:88-107; Spec `area`, `perimeter`, `sides`, `totalPrice`, `IsRegion`,
  `facesRegion`, `isFirstSection`; Proofs 8 files, 86 thms, ~47 lines).
- Noun: a region of garden plots with a plant letter.
- Proposal: `type Region = { plots: List Position }` with `Region.area`,
  `Region.perimeter garden`, `Region.sides garden`, `Region.price`. The program
  already has `Garden.regions`; spec `perimeter (region: List Position)` and the
  program `Garden.perimeter` are two definitions of the same thing, proved equal.
- Sketch:
  ```
  -- before
  def solvePart1 (garden: Garden): Nat := garden.regions |> .sumBy (region => region.length * garden.perimeter region)
  -- after
  def solvePart1 (garden: Garden): Nat := garden.regions.sumBy (region => region.area * region.perimeter garden)
  ```
- Benefit: statements read "area region * perimeter region". Cost: high (86
  thms); every `region ∈ …` membership lemma needs `.plots`. Do only if a proof
  lane is planned anyway. Score: **medium-high**.

### 2024/13 Offset naming (MEDIUM, cheap)
Local `type Offset = { x: Int, y: Int }` (Day13.sw:24) shares its name with
`Aoc.Common.Offset { rows, columns }` and used for button steps and prize
position (`Machine = { buttonA, buttonB, prize: Offset }`, Day13.sw:26). The
puzzle talks of X/Y, not rows/columns. Either rename (`Shift`/`Claw`/`Vec2`) or
make it the shared `Point`/`Delta` type (see Shared). `Offset.pressesToCover`
is already a method. 22 thms, only ~10 lines mention `.x`/`.y`. Score: **medium**
(cheap, mostly a rename).

### 2024/15 Cell (LOW)
`def Cell: Type := Offset` (Day15.sw:30) — cells as offsets from a corner so a step
is total (comment in file). The alias is a deliberate naming; it already has
methods (`Cell.gps`, `Cell.widen`). Keep. Score: **low**.

### 2024/16 Heading vs Direction (LOW-MEDIUM)
`Heading = East|South|West|North` with `toDirection` (Day16.sw:54,77) duplicates
Common `Direction`; the `Reindeer` record `{ position, facing: Heading }` is good.
Replacing `Heading` with `Direction` removes `toDirection` and `Heading.clockwise`
(= `Direction.turnRight`). Needs `Hashable/Ord Direction` for `Graph Reindeer`
keys. 5 Proofs files. Score: **low-medium**.

### 2024/17 Program (LOW)
`program: List Nat` in `Debugger` (Day17.sw:27) and threaded as `program: List Nat`
through `Machine.step`, `Machine.run`, `fuelFor`, `outcome`, Spec `StepMatches`,
`Halts`. `Program = { words: List Nat }` with `Program.fetch pointer`. 30 thms.
Score: **low**.

### 2024/18 MemorySpace in the spec (LOW-MEDIUM)
The program has `MemorySpace { size, corrupted }` but the spec states things on
`(size: Nat) (bytes: List Position) (count: Nat)` (`IsPath`, `HasPath`,
`IsFirstBlocking`; Spec.sw). `fallen`/`bytes` are really "the falling bytes";
`solvePart1 (size) (fallen) (bytes)` takes three raw args. `type Falling = { size, bytes }`
would give `Falling.after n` (= `MemorySpace.after`). Score: **low-medium**.

### 2024/19 Towel patterns and designs (LOW)
`def Pattern: Type := List Stripe`, `def Design: Type := List Stripe`
(Day19.sw:29,32) are aliases of the same type, so the compiler can't tell a
towel from a design. `Towel = { stripes }`, `Design = { stripes }`; methods
`Design.startsWith towel`, `Design.dropTowel`. 15 thms, ~28 lines. Score: **low**
(cheap, small benefit).

### 2024/21 Direction and Position copies (LOW)
Own `type Direction` (Day21.sw:22) and `type Position = { row, column }`
(Day21.sw:89) next to Common's identical names (not imported). Spec also uses
`List (List (Option k))` keypad rows. The keypad types (`NumericKey`,
`DirectionKey`, `Code`, `Keypad k`, `Costs`) are already good. Dedupe to
Common if cheap. 44 thms. Score: **low**.

### 2024/22 Buyers and secrets (LOW)
`List Nat` buyers/secret numbers/prices (Day22.sw:23,37,51). `Changes` is a
record already. A `Secret` wrapper would only carry `evolve`/`price`. Score: **low**.

### 2024/23 Computer and Connection (MEDIUM-HIGH)
- Raw: `def Computer: Type := Text` (Day23.sw:22), `(Computer, Computer)` connection,
  `Links = Map Computer (Set Computer)`, `Set Computer` for a party.
- Noun: a computer, a connection, a LAN party.
- Flows: program `connection`, `Network.bothWays`, `Network.links`, `Links.neighbours`,
  `mightBeChiefs`, `password`; Spec `connected`, `AllConnected`, `hasT`,
  `IsClique`, `IsLargest`, `password` (duplicated in Spec); Proofs 44 thms, ~91 lines.
- Proposal: `type Computer = { name: Text }` with `Computer.mightBeChief`
  (= `startsWith "t"`), `type Connection = { one: Computer, other: Computer }`,
  `type Party = { members: Set Computer }` with `Party.password`, `Party.hasChief`,
  `Party.size`. Program `mightBeChiefs` and Spec `hasT` become one method.
- Sketch:
  ```
  -- before
  def mightBeChiefs (set: Set Computer): Bool := set.any (computer => computer.startsWith "t")
  def password (party: Set Computer): Text := party.toList.sort.joinWith ","
  -- after
  def Party.mightHaveChief (party: Party): Bool := party.members.any .isChief
  def Party.password (party: Party): Text := party.members.toList.sort.joinWith ","
  ```
- Benefit: removes program/spec duplication (`password`, `hasT`). Cost: 91 lines
  mention `Computer`; wrap in a record forces `Ord` instance. Alias-with-methods
  is a zero-cost step. Score: **medium**.

### 2024/24 Wire, Gate, Device (GOOD)
Minor: `(Wire, Wire)` swap pairs (`swapOutputs`, `applySwaps`, `repair`) could be
`Swap { first, second }`; `fromBits: List Bool → Nat` is the shared Bits item.

Days 01, 02, 03, 06, 07, 08, 14, 20 good (01 `LocationLists`; 02 `Report`;
03 `Instruction`/`Tally`; 06 `Guard`/`Lab`/`Sightlines`; 07 `Equation`/
`Operator`; 08 `Antenna`/`City`; 14 `Robot`/`Space`/`Quadrant`; 20 `Racetrack`/`Cheat`).

---

## 2025

### 2025/03 Battery and Bank (LOW)
`def Battery: Type := Fin 10`, `def Bank: Type := List Battery` (Day03.sw:44,47)
with `Bank.best`, `Bank.maxJoltage` already methods. An alias already gives the
method home; a record `Bank = { batteries: List Battery }` would add safety only.
`joltageOf (on: List Battery)` (Day03.sw:38) could be `Battery.joltage`/`Bank.joltage`.
20 thms, ~53 lines. Score: **low**.

### 2025/06 Worksheet (LOW-MEDIUM)
Program has `Problem`, `Operator`; but `lines: List Text` / `List (List Char)`
(blocks of columns) are raw input shapes (`parseWorksheet`, `blocks`, `isBlank`),
and Spec statements are all in terms of `lines: List Text` plus column ranges
`(lo hi: Nat)`. `Worksheet = { lines: List Text }` with `Worksheet.column c`,
`Worksheet.blank c`, `Worksheet.problems` would put the spec's `charAt`/`column`/
`blank` where they belong. 29 thms, ~37 lines. Score: **low-medium**.

### 2025/08 Junction boxes by index (MEDIUM)
- Raw: `Nat` indices of boxes (`Connection.first/second`, `Circuits.labels : Map Nat Nat`,
  `Circuits.join first second`, `lastJoin : … → Option (Nat, Nat)`; Day08.sw:71-150),
  `List Point` indexed with `getOr … Point.origin` (Day08.sw:~140); Spec uses
  `(Nat, Nat)` pairs everywhere (`connectionOrder`, `Joined`, `Tells`, `xProduct`,
  Spec; ~110 lines, 68 thms).
- Noun: a junction box (identified by its position in the input), a circuit, a connection.
- Proposal: `type BoxId = { index: Nat }` (or `Fin n`), `type Link = { first: BoxId, second: BoxId }`
  (spec's `(Nat, Nat)`), `Circuits` methods already exist. `Boxes.at (id)` returns
  `Point` instead of `getOr … Point.origin`.
- Sketch:
  ```
  -- before
  |> .map (((first, second)) => (boxes.points.getOr first Point.origin).x * (boxes.points.getOr second Point.origin).x)
  -- after
  |> .map (link => (boxes.at link.first).x * (boxes.at link.second).x)
  ```
- Benefit: removes the `Point.origin` default; spec `xProduct` reads naturally.
  Cost: ~110 spec/proof lines. Score: **medium**.

### 2025/09 Rectangle and Edge (MEDIUM, cheap)
- Raw: `(Tile, Tile)` for both a rectangle's corners (`pairArea`, Day09.sw:52;
  Spec `rectangles`, `Part1`) and a loop line (`loopLines`, `Tile.isOnLine`,
  `crossesRightOf`, `touchesRow`, Day09.sw:64+; Spec `connections`, `onStraightLine`,
  `crossesRay`), and `(Corner, Corner)` (`Floor.allRedOrGreen`, `cornersArea`).
- Noun: a rectangle (two opposite red tiles), a side of the loop.
- Proposal: `type Rectangle = { corner: Tile, opposite: Tile }` with `Rectangle.area`;
  `type Edge = { from: Tile, to: Tile }` with `Edge.contains tile`, `Edge.crossesRay`;
  `Tile.isBetween`. See Shared (Point/Segment).
- Sketch:
  ```
  -- before
  def pairArea (corners: (Tile, Tile)): Nat := area corners.fst corners.snd
  def solvePart1 (tiles: List Tile): Nat := tiles.pairs |> .map pairArea |> largest
  -- after
  def Rectangle.area (r: Rectangle): Nat := (Nat.absDiff r.corner.x r.opposite.x + 1) * (Nat.absDiff r.corner.y r.opposite.y + 1)
  def solvePart1 (tiles: List Tile): Nat := tiles.rectangles |> .map .area |> largest
  ```
- Benefit: `.fst`/`.snd` disappear; area/containment as methods. Cost: low (~13
  Spec lines, 31 thms, mostly use `Tile` fields). Score: **medium**.

Days 01 (Dial/Turn), 02 (Range, RepetitionTemplate), 04 (Cell/Grid, Vec grid),
05 (Database + Range), 07 (Manifold) are good. 2025/04 and 2025/07 use
size-indexed `Vec` grids that Common `Grid` doesn't cover; leave.

---

## Shared shapes for Aoc.Common

Common today: `Grid a`, `Position {row, column}`, `Direction`, `Offset {rows, columns}`,
`Range {from, to}`, `GridGraph`.

1. **`Bits`** (or `BitString`): `{ bits: List Bool }`, most significant first, with
   `Bits.value : Nat` (`Nat.fromBits`), `Bits.width`, `Bits.ofNat width n`,
   `Bits.complement`, `Bits.take`. Used by 2020/05 `Pass` (SW-1282 would be a
   thin wrapper or an instance), 2021/03 `Bits`, 2021/16 transmission and
   fields, 2024/24 `fromBits`/`zBits`. Medium value; makes day 5 and 2021/03 agree.
2. **`Point {x, y}`** and **`Segment {from, to}`**: 2021/05 `Point = (Nat, Nat)`
   and `Line`; 2021/13 `Dot` (with `Ord`); 2025/09 `Tile`; 2024/13 `Offset {x, y: Int}`
   as a vector. The puzzle language on these days is x/y, not row/column, so
   `Position` doesn't fit. Methods: `Point.manhattan`, `Point.absDiff`, `Segment.isStraight`,
   `Segment.isDiagonal`, `Segment.contains`. 2025/08 `Point` is 3-D; leave it.
3. **Interval helpers**: Common `Range` requires `from ≤ to` and has `contains`,
   `size`. Re-implemented around it: 2021/05 `between`, 2025/09 `isBetween`/
   `isBetweenHalfOpen`/Spec `from`, 2021/07 `distance`, 2021/17 `Target` (two
   `Int` intervals), 2024/09 `Span {start, length}`. Add `Range.ofEnds a b`
   (sorted), `Range.containsHalfOpen`, and perhaps an `Int` version. Low-medium.
4. **Undirected edges / adjacency**: 2021/12 `(Text, Text)` + `neighbourTable`,
   2024/23 `(Computer, Computer)` + `bothWays`/`links`, 2025/08 `Connection`.
   Common `Edge a = { one: a, other: a }`, `Edge.reverse`, `adjacency : List (Edge a) → Map a (Set a)`.
   Medium.
5. **Grid wrappers**: 2021/09 HeightMap, 2021/15 Cave, 2024/10 TopographicMap
   each hold `rows` and duplicate `Grid`; 2021/11 and 2024/04 don't use `Grid`
   at all. Decide: a domain record holding `grid: Grid Cell` (cells typed as
   domain, e.g. `Grid Height`) and delegating `at/step/cells/graph`. Also a
   Common `Grid.findOnly (cell)` replacing the identical `onlyTile` in
   2024/16 (Day16.sw:37) and 2024/20 (Day20.sw:44), and the near-identical
   `Maze`/`Racetrack` (open tiles `Set Position`, `start`, `end`) shape.
6. **Direction duplicates**: 2024/16 `Heading`, 2024/21 `Direction`, 2024/04
   Spec `Direction {down, across}` (8-way). Common could offer `Direction.all8`/
   `Offset`-based `Direction8`. Low.

Not types, but repeated: "three largest, multiplied" (2021/09 `largestThreeProduct`,
2025/08 `threeLargestProduct` x2: program + Spec); a `middle` of a sorted list
(2021/10 `middle`, 2024/05 `Update.middlePage`).

---

## Patterns

- **Transparent aliases vs records.** `type Bits = List Bool`, `Board`, `Point`,
  `PairCounts`, `Values`; `def Computer/Pattern/Design/Battery/Bank/Cell/Links/
  FreeSpace: Type := …`. These are the cheapest first step (name + dot methods,
  no proof churn) but nothing stops a `Design` being used as a `Pattern`
  (2024/19 declares both as `List Stripe`). Decide per day.
- **Program has the record, spec/proofs go back to raw.** 2024/05 (`pages`),
  2024/12 (`List Position` vs `Garden.regions`), 2024/18 (`size`/`bytes` vs
  `MemorySpace`), 2021/12 (`List Text`), 2024/23 (`password`, `hasT` duplicated).
  Fixing the spec to use the program's type is the lowest-risk kind of refactor
  (proofs change by renaming only).
- **Tuples carrying meaning.** `(Text, Text)` passage, `(Char, Char)` pair,
  `(Tile, Tile)` rectangle/edge, `(Nat, Nat)` link/range/point, `(Wire, Wire)`
  swap. `.fst`/`.snd` is the tell. Cost per tuple is usually low because proofs
  seldom open them.
- **`List (List a)` rows by hand.** 2021/11 (two grids), 2024/04, 2021/09,
  2021/15, 2024/10: grids re-modelled instead of using Common `Grid`.
- **`Option Nat` meaning two things.** 2024/09 blocks (`Some id`/`None`),
  2024/10 heights, 2025/06 `operator: Option Operator` (this one is fine).
- **Magic strings.** `"start"`/`"end"` in 2021/12; `"t"` prefix in 2024/23.
- **Spec duplicates program helpers** (`password`, `gridWidth`, `threeLargestProduct`,
  `bitSet`/`BitwiseXor` in both 2024/17 and 2024/22). Domain methods give one
  home, and the equivalence proofs shrink.
- **Proof-lane sizing.** Of the high/medium list, the ones with <=15 spec lines
  and <=35 thms (2021/04, 2025/09, 2024/13, 2021/14, 2024/19) can be done by a
  Sonnet or DeepSeek lane; 2021/11, 2021/12, 2024/12, 2021/16 touch 44-86 thms
  and belong in an Opus proof lane (and `task audit:touched`).

---

## Coverage: days with nothing worth doing

2020: 01 (trivial), 02, 03, 04. (05 is SW-1282.)
2021: 01 (trivial), 02, 08, 17, 18 (13 and 15 only minor items above).
2024: 01, 02, 03, 06, 07, 08, 14, 20, 24 (minor swap-pair note).
2025: 01, 02, 04, 05, 07.

Not covered in depth: no day was skipped entirely. I did not read 2021/16's and
2024/21's and 2024/24's program bodies or any Proofs bodies beyond grep counts
and theorem names, so their scores are by signature only. Counts of "thms" are
`^theorem` lines (excluding `def`-statements such as `Part1Answer` Props), and
overstate churn where many theorems are about functions that don't mention the
raw type.
