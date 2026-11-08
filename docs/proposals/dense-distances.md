# Proposal: Dijkstra over an array, for states with a dense index

**Status:** draft 2, 8 November 2026. Ticket SW-2377 (paper lane, Opus);
revised by SW-2394 after Matt's decisions D3416 (yes, std gets the
array-backed search), D3417 (one function, `Graph.distances`, with an
optional named `index`), D3418 (moot: the result is a `Map`, as today). The
index's shape was D3419, (b). Stage 1 ([§9](#9-plan-and-estimate)) was
built by SW-2394, stages 2 and 2b by SW-2396 (§4.4, "As built").
Draft 1's two-function design (`Graph.distancesIndexed` beside
`distances`, proved equal to it) is kept below, marked **superseded**, for
its reasoning. Numbers are taken from
[SW-2369](../reviews/SW-2369-dijkstra-disk.md),
[SW-2371](../reviews/SW-2371-map-rebuild-reuse.md) and the SW-2370 and
SW-2382 lane reports on the board, and are marked **[measured]** (with
where) or **[estimated]** (with how). Code is as of `ca232293a`:
`crates/elab/src/std/Graph/Search.sw` after SW-2370 (improvement-only
pushes with a `best` map), SW-2382 (`searchFrom` takes the popped pair) and
SW-2376 (`reachable` by breadth-first search).

## 0. Summary

- **The problem.** 2021 day 15 runs std's verified `Graph.distances` over
  260,000 grid positions. Its cost tables (`settled`, `best`) are tree
  `Map`s keyed by `Position`. With tonight's fixes it is about 3.0 s native
  against CPython's 0.5 s and Lean's 0.2 s. SW-2369 measured the same search
  by hand with the costs in an `Array` at **half the time** of the
  `Map` version (2.47 s to 1.19 s, same loaded machine).
- **The change.** Make the search generic over a small, lawful **cost
  table** (`Graph.Costs`: `empty`, `get`, `set` and three laws), so one
  proof covers every table (stage 1). Then give `Graph.distances` an
  optional named argument, `index`, that numbers states densely: `graph.distances
  sources` is today's search, and `graph.distances (index := grid.index)
  sources` keeps numbered states' costs in an `Array` and the rest in a side
  `Map` ([§4.4](#44-one-function-distances-with-an-optional-index), D3417).
  It returns a `Map`, as now. The theorems take the same optional `index`,
  so every one of them already speaks about the indexed call: no equality
  theorem, no rewrite in callers' proofs.
- **What it should do.** Day 15 from about 3.0 s to about 1.4-1.5 s
  native **[estimated]**, about 3x CPython rather than 6x; nothing else
  changes speed (stage 1 is measured not to slow `distances`). The caller
  proves two facts about its index (decoding a state's number gives it
  back, and numbers are below the size), which for a grid is a `Nat`
  division lemma std already has, its remainder partner and a short bound.
- **Work.** About three lane-hours in two Opus lanes and one Sonnet lane
  ([§9](#9-plan-and-estimate)).

## 1. The problem

### 1.1 Numbers

| Program (2021 day 15, both parts) | Native time | Where |
|---|---:|---|
| stock `Graph.distances` before tonight | 5.49 s (loaded machine) | SW-2369 §1.3 **[measured]** |
| after SW-2370 (push only improvements) | 3.50 s (loaded) | SW-2370 lane **[measured]** |
| after SW-2382 (popped pair, no queue argument) | 3.03-3.05 s, 48.4 G instructions | SW-2382 lane, `bench:compare --runs 3` **[measured]** |
| E5: by hand, improvements, `Map` costs | 2.47 s (loaded) | SW-2369 §1.3 **[measured]** |
| E3: by hand, improvements, `Array` costs | 1.19 s (loaded) | SW-2369 §1.3 **[measured]** |
| E1: E3 with a packed `Nat` queue key | 0.86 s (loaded) | SW-2369 §1.3 **[measured]** |
| CPython (`bench/compare/dijkstra/main.py`) | 0.50 s (loaded), 0.84 s (Overmind) | SW-2369 **[measured]** |
| Lean (`bench/compare/lean/Compare/Dijkstra.lean`) | 0.20 s (Overmind) | SW-2295 via SW-2369 **[measured]** |

E5 is the algorithm std now runs (SW-2370 made `distances` push only
improvements), so E5 to E3 is what a dense table is worth on top of
tonight's work: **2.47 s to 1.19 s, a factor of 2.1** on the same machine
and run. Applied to the current 3.03 s that is about **1.45 s
[estimated]** (ratio carried over; the E-variants were hand-written and
skipped the proof parameters, so the stock program may keep a little more
overhead).

### 1.2 Why the tables cost so much

Per settled state the search reads `settled` once per pop and `best` once
per edge, and writes each once per improvement: about 1.3 M table
operations on day 15 (260 k pops, 1.04 M edges, 260 k settles plus the
improvements) **[estimated from SW-2369's counts]**. Each is a walk of a
balanced tree of up to 260 k `Position` keys, 17-19 levels, each level a
`Position.%compare` through the `Ord` dictionary, and each write a path copy
whose old nodes are freed (SW-2369 rows 1-3: tree work, freeing and key
comparison were 64% of self time). An `Array` read or write is one bounds
check and one load or store, in place when the array is unshared
(`std/Array/Array.sw`, "Cost").

### 1.3 Who else would use it

Graph searches over grid-shaped states in `aoc/`: 2021 day 15 (`Position`,
`distances`), 2024 day 16 (`Reindeer`: a position and a facing, so
`4 * (row * width + column) + facing`; `distances` twice, and it reads the
whole result with `toList`), and the breadth-first users 2021 day 9, 2024
days 18 and 20 (`breadthFirst` keeps a `Map s Nat` too). Only day 15 and
day 16 are in scope here; breadth-first search is [§9](#9-plan-and-estimate)'s
stage 3.

## 2. The options

**A. A separate `Graph.distancesDense`.** Copy `searchFrom` and its proofs
(about 450 lines of `Search.sw`: `relaxEdges` and five `relax*` lemmas,
`Pending`, `SearchState`, `pendingKept`, `skipKeeps`, `settleKeeps`,
`searchFromCorrect`, `distancesCorrect`), replacing the 41 uses of `Map`
lemmas with `Array` ones. Simple to start, but two copies of the hardest
proof in std, and every later change (a heap queue, packed keys, the
SW-2388 lowering fix's restatements) is made twice.

**B. One search over a cost table (recommended).** Generalise the search
over a record of operations and laws that both `Map s Nat` and an indexed
array satisfy. The proofs are written once against the laws; `distances`
is the search at the `Map` table, so its public statements don't change;
the dense search is the same function at the array table. A later hash map
or a packed table plugs in the same way.

**C. Leave it to AoC code (`Aoc.Common`).** A grid Dijkstra in
`Aoc.Common` with its own proof. This duplicates option A's proof outside
std, where it can't serve non-AoC programs, against the rich-std direction
(Matt, 7 Nov 2026), and day 15's proofs would have to be restated against
it. Its only advantage is freedom to specialise (packed keys, no
`Ord Position`), which option B can reach later ([§9](#9-plan-and-estimate)
stage 3).

**D. Wait for the runtime.** SW-2388 (argument clones in lowering), node
reuse in `Map.Tree` (SW-2371 B/C) and a `Std.Heap` all make the `Map`
version cheaper, but none changes a 17-level keyed walk into one load.
SW-2371 put reuse at about 6% and SW-2382 got 2%; E5 to E3 is 52%. They are
worth doing anyway and are complementary.

## 3. The cost table (option B)

```stitchwort
--| A table of costs by state, as the search keeps them: `settled` and
--| `best`. Any table whose `get` sees each `set` will do.
type Graph.Costs (s: Type) (t: Type) = {
  empty: t,
  get: t → s → Option Nat,
  set: t → s → Nat → t,
  getEmpty: (state: s) → get empty state = None,
  getSet: (table: t) → (state: s) → (cost: Nat) → get (set table state cost) state = Some cost,
  getSetOther: (table: t) → (state: s) → (cost: Nat) → (other: s) → other ≠ state →
    get (set table state cost) other = get table other
}
```

That is the whole interface the proofs need. Every `Map` fact the search
uses today follows from these three laws: `getInsertCases`,
`getInsertKeeps`, `containsInsertKeeps`, `containsInsertSame` and
`getOfContains` are each a two-line consequence (with `contains` as
`(get table state).isSome`). The case splits on `state == next` stay as
they are, since the queue is still a `Set (Nat, s)` and so `Ord s` (and its
`DecEq`) is still around.

- **The `Map` table:** `Graph.mapCosts: Graph.Costs s (Map s Nat)` from
  `Map.empty`, `Map.get`, `Map.insert` and `Map.getEmpty`, `Map.getInsert`,
  `Map.getInsertOther`. `get` is `Map.get` by definition.
- **The indexed table** ([§4](#4-the-index-and-the-indexed-table)).

What changes in the proofs: `searchFrom`, `relaxEdges`, `improves`,
`unsettledIn`, `Bound`, `Pending` and `SearchState` take `costs:
Graph.Costs s t` and use `costs.get`/`costs.set`, and the 41 `Map.*` lemma
uses become uses of the three laws or the five consequences. The shape of
every argument stays: same invariant, same measure (`unsettledIn` over
`costs.get … |>.isSome`), same lexicographic decrease. This is the kind of
mechanical-but-proof-heavy edit SW-2370 did in 12 minutes on the same
file.

**Public statements stay put.** `Bound`, `SearchResult` and `Shortest`
are stated about a `Map`, and stage 1 leaves their definitions as they
are. Beside them are `…By` forms over a lookup function, `Graph.BoundBy
get cost state` and `Graph.SearchResultBy graph sources reach get`, which
the generic proof concludes; at the `Map` table, `Graph.mapCosts.get
result` computes to `result.get`, so the generic conclusion *is*
`SearchResult graph sources reach result` and `distancesCorrect` is one
line, with no rewrite. `distancesShortest`, `boundAlong`, `reachableIff`
and the AoC proofs check unchanged. (Draft 1 had `SearchResult` become a
wrapper over `SearchResultBy`; keeping it as it was is simpler and leaves
its hash alone.)

**As built (SW-2394).** `Graph.Costs` has the three laws above, each with a
doc. Its derived facts are `Graph.Costs.has` (whether the table has a
cost: a `match` on `get`, as `Map.contains` is) with `hasOfGet`,
`getOfHas`, `hasSetSame`, `hasSetKeeps`, `getSetCases` and `getSetKeeps`.
`Graph.distancesWith graph costs sources` is the search at any table, and
`Graph.distancesWithCorrect` its `SearchResultBy`; `distances` is
`distancesWith` at `Graph.mapCosts`. The search's internal pieces
(`improves`, `relaxEdges` and its five lemmas, `Pending`, `SearchState`,
`pendingKept`, `boundOfPending`, `skipKeeps`, `settleKeeps`,
`searchFrom`, `searchFromCorrect`, `startQueued`, `relaxedQueued`) take
`costs` and a table type `t`; the measure is `Graph.unsettledAt costs`,
and breadth-first search keeps `Graph.unsettledIn` on its `Map`.

**Run-time cost of the generality.** `costs.get` is a call through a record
field, as `Ord`'s `compare` already is; about 2 M such calls on day 15, a
few tens of milliseconds at the closure-call costs SW-2369 measured (14.5 M
`sw_apply_cached` in 5.3% of 5.5 s) **[estimated]**. Measured after stage
1 (`task bench:compare -- --runs 3 --runners native --instructions
dijkstra`, same machine, minutes apart): 44.01 G instructions and 3.02 s
before, **41.62 G and 2.83 s after**, 5% fewer **[measured]**. Not slower,
then; why it is faster wasn't looked into (a guess: `has` matches on the
`Option` where `Map.contains` was a call more).

## 4. The index and the indexed table

### 4.1 What the caller gives

**Draft 1's shape, kept for its reasoning; D3419 ([§8](#8-open-questions))
asks which shape to build.** One finding since draft 1 bears on it: `Fin n`
is a unary data type (`FZero`, `FSucc`, `std/Fin/Fin.sw`) with no native
representation, so `Fin.toNat` on cell 200,000 walks 200,000 constructors.
An index that hands the search a `Fin n` would cost far more than the
tree walk it replaces. Whatever the shape, the number the search uses at
run time must be a `Nat`, with its bound as an erased proof.

```stitchwort
--| Numbers some states `0` to `n - 1`, each with its own number: decoding
--| a state's number gives the state back. States without a number are
--| allowed.
type Index (s: Type) (n: Nat) = {
  toFin: s → Option (Fin n),
  fromFin: Fin n → s,
  roundTrip: (state: s) → (i: Fin n) → toFin state = Some i → fromFin i = state
}
```

- **In range** is the type: `toFin` returns a `Fin n`, so the array of
  size `n` always has the cell. No separate obligation.
- **Injective** follows from `roundTrip` in one line (`a = fromFin i = b`).
  A left inverse is asked for instead of an injectivity proof because it is
  easier to prove by computation (decode the encoding) than injectivity is
  by cases, and because `fromFin` is useful twice more: it lists the
  result's keys in index order ([§5](#5-the-result-a-map-built-at-the-end)),
  and it is what a packed `Nat` queue key needs later (stage 3).
- **Covering** the states is *not* asked for. A state with no number goes
  in a small `Map` beside the array, so the table's laws hold for every
  state and the search's proof never asks which states have numbers. For a
  grid every state has one and the side map stays empty; the cost is one
  branch per operation. The alternative, a coverage proof (`state ∈
  graph.universe sources → (index.toFin state).isSome`), would put a domain
  condition on every law and into `SearchState`; D3419 asks.

For a grid, in `Aoc.Common` beside `Position`:

```stitchwort
def Position.boxIndex (height: Nat) (width: Nat): Index Position (height * width) := {
  toFin = position => if inside: position.within height width then Some (Fin.ofNatLt _ (position.row * width + position.column) (…)) else None,
  fromFin = i => { row = i.toNat / width, column = i.toNat % width },
  roundTrip = …
}
```

`roundTrip` is `Nat.mulAddDivSmall` (`(row * width + column) / width =
row` when `column < width`, `std/Nat/Arith.sw:641`) and a `%` partner
(`(row * width + column) % width = column`, from `Nat.divModEq`; a short
new std lemma if none exists);
the in-range proof is `row * width + column < height * width` from `row <
height` and `column < width`, a short `Nat` lemma (omega can't multiply by
a variable). Day 16's `Reindeer` index is the same with a factor 4.

### 4.2 The table

```stitchwort
--| Costs in an array cell per numbered state, and a map for the rest.
type Graph.IndexedCosts (s: Type) (n: Nat) [ord: Ord s] = {
  cells: Array (Option Nat),
  sized: cells.size = n,
  rest: Map s Nat
}

def Graph.indexedCosts [auto ord: Ord s] (index: Index s n): Graph.Costs s (Graph.IndexedCosts s n)
```

(Draft 1's names; under the recommended D3419 shape the table takes a
`Graph.Index s` and holds its size in the index, not the type.) `get`
reads `cells` at `toFin state` (or `rest` when `None`); `set` writes
there. `sized` is what makes `getSet` hold for every table (`Array.getSet`
needs the index below the size; `Array.sizeSet` keeps it); it is a proof
field, so it is erased at run time (erase-proof-data.md, "The problem, plainly"). The laws
come from `Array.getSet`, `Array.getSetOther` (two different numbers, by
`roundTrip`), and the `Map` laws for `rest`.

### 4.3 The search (superseded by D3417)

**Superseded.** Matt chose one function, not two (D3417): see
[§4.4](#44-one-function-distances-with-an-optional-index). Draft 1's
second function is kept here for the record.

```stitchwort
--| `graph.distances sources`, with the search's cost tables kept in arrays
--| of `n` cells, one per state `index` numbers: for graphs such as grids
--| whose states are numbered densely. States `index` doesn't number still
--| work, kept in a map. [`Graph.distancesIndexedEq`] says it is `distances`.
def Graph.distancesIndexed [auto ord: Ord s] (graph: Graph s) (index: Index s n) (sources: List (s, Nat)): Map s Nat

theorem Graph.distancesIndexedEq [auto ord: Ord s] (graph: Graph s) (index: Index s n) (sources: List (s, Nat)):
    graph.distancesIndexed index sources = graph.distances sources
```

Day 15 would have become `risks.graph.distancesIndexed (Position.boxIndex
risks.height risks.width) [(risks.start, 0)]`, its proofs starting with
`rewrite Graph.distancesIndexedEq`.

### 4.4 One function: `distances` with an optional index

A `def`'s explicit parameter may have a default, given by name only
(`docs/syntax.md`, "Parameter defaults"): positional arguments skip it, and
every written call that leaves it out fills it. So `distances` gains one
parameter, between the graph and the sources:

```stitchwort
--| The least cost to each state reachable from one of the sources, each
--| given with the cost of starting there. With an `index` that numbers the
--| states densely, such as a grid's cells, the search keeps the numbered
--| states' costs in arrays rather than maps, which is about twice as fast;
--| the result is the same.
def Graph.distances [auto ord: Ord s] (graph: Graph s) (index: Graph.Index s := Graph.Index.none)
    (sources: List (s, Nat)): Map s Nat
```

- **Callers.** `graph.distances sources` (day 15 now, `Aoc.Common`'s grid
  test) and `maze.graph … |> .distances sources` (day 16) are unchanged:
  the default fills in. Day 15 becomes `risks.graph.distances (index :=
  risks.index) [(risks.start, 0)]`. The default's identity is a generated
  `Graph.distances.index%default`, so a call that leaves it out has a new
  hash; migration cost doesn't count (D2303).
- **The default.** `Graph.Index.none` numbers nothing (its size is 0).
  `distances` picks the table once, at the top: an index of size 0 runs the
  search at the `Map` table, which is exactly today's search, with no
  per-operation branch; any other index runs it at the indexed table. Both
  are instances of the one generic search of stage 1, so one proof covers
  both branches.
- **The theorems take the same optional `index`.** `distancesCorrect`,
  `distancesShortest` gain `(index: Graph.Index s := Graph.Index.none)` in
  the same place, and their conclusions are about `graph.distances (index
  := index) sources`. Every existing use (`Graph.distancesShortest
  risks.graph sources`, `Graph.distancesCorrect (maze.graph False) … reach
  …`) fills the default and states what it states today; a caller using an
  index passes the same one: `Graph.distancesShortest risks.graph (index :=
  risks.index) sources`. Day 15's proofs change only in that argument.
- **`reachable` and `reachableIff`** don't change: they are breadth-first
  (SW-2376). Giving `breadthFirst` the same argument is stage 3.
- **What replaces the equality theorem.** Nothing is needed for callers:
  each theorem is already about the indexed call. Inside the proof, the
  indexed branch needs one lemma, that the `Map` built at the end has the
  table's `get` (§5, step 3), which turns the generic `SearchResultBy` on
  the table into `SearchResult` on the map. The uniqueness lemma
  (`Graph.shortestUnique`, two `Shortest` maps for the same graph and
  sources are equal; [§5](#5-the-result-a-map-built-at-the-end)) is no
  longer on the path. It would give `graph.distances (index := i) sources
  = graph.distances sources` in a few lines, which is worth adding only if
  a caller wants to move between the two calls inside a proof; none does.

**As built (SW-2396, stage 2).** D3419 went to (b), with one change:
`decode: Nat → Option s` (with `roundTrip` giving `Some state`), since
`Graph.Index.none` must exist for every `s`, an empty one included, and so
can't decode to an `s`. The table is `Graph.IndexTable s index` (`cells`,
`rest`, and three erased proofs: the size, each cell with a cost belongs to
the state its number decodes to, and `rest` holds only unnumbered states),
whose laws are `Graph.indexCosts`; `Graph.IndexTable.getToMap` is §5's
lemma. `distances` matches on `index.size`: `Zero` is stage 1's map search,
`Succ` calls `Graph.distancesByIndex`. Two run-time findings: the table's
`set` takes the record apart with a `match` (projecting `cells` then `rest`
kept the old table holding the array, and every `set` copied it), and the
indexed branch has to be a call, so that `distances` stays small enough to
be inlined and the map branch keeps its `Ord` specialisation (otherwise 6%
more instructions on the map path). Each search makes two copies in all,
one per table, from the empty table the `Graph.Costs` record holds, and
none per operation (`an_indexed_search_changes_its_tables_in_place`). Day
15 native **[measured]**, `bench:compare --runs 3 --instructions`: 2.69 s
and 41.56 G instructions before, 1.26-1.30 s and 19.65-19.69 G after; the
map path (day 15 without the index) 41.57 G.

## 5. The result: a `Map` built at the end

The search finishes with the settled table; the indexed branch of
`distances` ([§4.4](#44-one-function-distances-with-an-optional-index))
turns it
into a `Map s Nat`: the array's `Some` cells, decoded by `fromFin`, in index
order, then the side map's entries. `Map.fromList` is O(n) when the keys
come ascending (`Map.Raw.fromListFast`, `std/Map/Spec.sw:1463`), and for a
grid they do: index order is row then column, which is `Position`'s order.
Otherwise it falls back to O(n log n), still correct.

- **Cost:** a few list passes and 260 k tree nodes on day 15, about 0.05-0.1
  s **[estimated: about 1.5 M cells at SW-2371's 45 ns per cell]**, under a
  tenth of the search.
- **Why a `Map` and not a view** (a `get` over the array): it is the type
  `distances` returns, so it is a drop-in. Day 16 reads the whole result
  (`fromStart.toList`), and every lemma about `Map` applies. A view saves
  the build (day 15 reads one entry) but needs its own `get`, `toList` and
  lemmas, and every caller's types change. Q3.

**Why it equals `distances` (superseded by D3417).** With one function
whose theorems take the index ([§4.4](#44-one-function-distances-with-an-optional-index)),
no equality theorem is needed; of the steps below only 2 and 3 remain, and
step 3 is the lemma the indexed branch uses. Draft 1's argument: two maps that both satisfy `Graph.Shortest`
for the same graph and sources are equal: if one has `cost` for a state,
that cost is some walk's (first half of `Shortest`), so the other has the
state for no more (second half), and the same the other way, so the costs
are equal; if one has no entry where the other has, the other's entry is a
walk's, so the first would have one too. Then `Map.ext`
(`std/Map/Map.sw:366`). So the proof of `distancesIndexedEq` is:

1. `Graph.shortestUnique: Shortest graph sources a → Shortest graph sources
   b → a = b`, about 30 lines, public (it is a useful fact in itself);
2. the generic search's `SearchResultBy` at the indexed table, from the one
   proof of §3, then `Shortest` through `shortestOfResult`;
3. one lemma that the built `Map`'s `get` is the table's `get`
   (`Map.getFromList`, `std/Map/Map.sw:635`, plus `roundTrip` to say each
   key appears once);
4. `shortestUnique` with `distancesShortest`.

That equality was why draft 1 didn't need a second public spec. Under
D3417 the reason is simpler: there is only one function.

## 6. Python and Lean

| | Python (`main.py`) | Lean (`Dijkstra.lean`) | Stitchwort, this note |
|---|---|---|---|
| Costs so far | `dict` keyed by `(row, column)` | `Array Nat` of `size`, `∞` = 2^60, `set!` | `Array (Option Nat)` of `height * width` (`best`), and another (`settled`) |
| Stale pop | `risk > cost[(row, column)]` | `cost > distance[here]!` | `settled` cell is `Some` |
| Queue | `heapq` of `(risk, row, column)` | `TreeSet Nat`, key `distance * size + position` | `Set (Nat, Position)`, unchanged |
| Index | none (hashing) | `row * width + column`, unchecked | `Position.boxIndex`, with `roundTrip` proved |
| Proved | nothing | nothing (`!` reads panic out of range) | `distancesCorrect`/`distancesShortest` at the given index |
| Time | 0.50 s (loaded) | 0.20 s (Overmind) | about 1.45 s **[estimated]** |

What still separates Stitchwort from Lean after this: the queue's pair
compare through `Ord` closures (E3 to E1, 28%), the second table (Lean
needs no `settled`: with improvement-only pushes, a pop is stale exactly
when its cost is above `best`), and the runtime's allocation per tree
update (SW-2369 §1.3, the last 4x). The fairness question SW-2369 §3.1
raised (a verified generic search against hand-written loops) is answered
the way that keeps the verified story: the Stitchwort program uses the
same data structure Lean's does, through std's proved search.

## 7. Risks

1. **A shared array copies on every `set`.** This is the one that matters:
   a tree `Map` that is shared costs a path copy, an `Array` that is shared
   costs a 260 k-cell copy, and 500 k sets of that is minutes. SW-2382
   found that `relaxEdges`' inlined `queue.insert` passes clones rather
   than moves (SW-2388, lowering), and `relaxEdges` returns `(queue, best)`
   that `searchFrom` projects twice (`relaxed.snd`, `relaxed.fst.popMin`).
   The dense lane destructures the pair once, and its acceptance test is
   `stitchwort run`'s array-copy count on day 15: zero copies, or the lane
   stops and reports. E3 shows the pattern can be unshared; SW-2388 may be
   a prerequisite.
2. **The `Map` version gets slower.** Indirect calls through `Graph.Costs`
   ([§3](#3-the-cost-table-option-b)); stage 1 measures `bench:compare`
   dijkstra and needs it within noise.
3. **JS.** Arrays under `--js` are version arrays (SW-1638), O(1) when each
   version is used once, so the playground gets the same shape of gain.
   (`std/Array/Array.sw`'s doc still says "Under `--js` every operation
   runs as written, on the list", which SW-1638 made untrue.)
4. **Proof size.** Generalising touches every lemma in the Dijkstra half of
   `Search.sw`; it is mechanical, but it is the kernel-checked core of the
   search, so it is an Opus lane and gets `audit:touched -- Std.Graph`.

## 8. Open questions

Draft 1's Q1-Q3 are decided; Q4 is now D3419, still open.

- **Q1 (D3416, decided: yes).** Std gets the array-backed search, as one
  search over a cost table (option B).
- **Q2 (D3417, decided: one function).** No second name:
  `graph.distances (index := …) sources`
  ([§4.4](#44-one-function-distances-with-an-optional-index)).
- **Q3 (D3418, moot).** It returns a `Map`, as today.
- **D3419. The index's shape.** What a caller passes as `index`. The search
  needs: a size; for each state, a cell number below the size or none; and
  one fact that makes two numbered states with the same number equal. Its
  run time needs the number as a `Nat` (§4.1: `Fin` is unary). The
  options:

  - **(a) Draft 1's `Index s n`**: `toFin: s → Option (Fin n)`, `fromFin`,
    `roundTrip`, the size in the type. Out: `Fin` costs O(number) at run
    time, and the size in the type means `distances` needs an implicit
    `[n: Nat]` beside a defaulted `index`, which implicit parameters can't
    have defaults for (`docs/syntax.md`, "Where defaults can't go"), so the
    default would have to fix `n` by unification.
  - **(b) A record with its size inside, numbers as `Nat` (recommended):**

    ```stitchwort
    --| Numbers some states from `0` to `size - 1`, each with its own
    --| number: decoding a state's number gives the state back. States
    --| without a number are allowed.
    type Graph.Index (s: Type) = {
      size: Nat,
      number: s → Option Nat,
      decode: Nat → s,
      below: (state: s) → (i: Nat) → number state = Some i → i < size,
      roundTrip: (state: s) → (i: Nat) → number state = Some i → decode i = state
    }
    ```

    The proofs are erased, so at run time
    it is a size and two closures. `Graph.Index.none` is `{ size = 0,
    number = _ => None, … }`, and `index.size == 0` selects the plain `Map`
    table, so the default costs nothing. For a grid, `below` is `row *
    width + column < height * width` and `roundTrip` is
    `Nat.mulAddDivSmall` with its `%` partner, as §4.1 says. Injectivity
    follows from `roundTrip` in one line; `decode` also lists the
    result in index order (§5) and gives packed queue keys later (stage 3).
  - **(c) As (b) without `state` and `roundTrip`, with an injectivity
    field** (`number a = Some i → number b = Some i → a = b`). Smaller, but
    the result `Map` then can't be built from the array alone: the cells
    would have to hold the state too (`Array (Option (s, Nat))`), twice the
    memory and a key copy per settle, or the result is built by walking
    `graph.universe sources`, which is O(n log n) and needs every reached
    state listed. And injectivity is harder to prove for a grid than a
    decoding is to compute.
  - **(d) No `below`: the search checks `i < cells.size` at run time** and
    falls back to the side map. One obligation fewer, one compare per
    operation more (negligible beside the array load), and a wrong index
    silently runs at map speed instead of failing to check. Could be
    combined with (b).

  **[rec: (b).** Two short proofs for a grid, both by computation; a plain
  `Nat` at run time; the size travels with the index so the default needs
  no implicit parameter; decoding gives the result in order without
  storing states. Name it `Graph.Index` for now, in `Std.Graph`; it moves
  to its own namespace if a dense set or table outside graphs wants it.
  The grid instance goes in `Aoc.Common` beside `Position`, and moves to
  std with a std `Grid` (arrays.md Q8).**]**

## 9. Plan and estimate

| Stage | Work | Who | Estimate |
|---|---|---|---|
| 1 (SW-2394) | `Graph.Costs` and its laws; the Dijkstra half of `Search.sw` generalised over it; `Graph.mapCosts`; `distances` at it; `…By` forms of `Bound` and `SearchResult` for the generic proof, the public ones unchanged. `bench:compare` dijkstra within 2%; `audit:touched -- Std.Graph`. | Opus | 90 min |
| 2 | After D3419: `Graph.Index`, `Graph.Index.none`, the indexed table and its laws, `distances`' optional `index` (the `size == 0` dispatch), the same argument on `distancesCorrect` and `distancesShortest`, the built `Map`'s `get` lemma; zero array copies on day 15 (or stop: SW-2388 first). | Opus | 60-90 min |
| 2b | The grid index in `Aoc.Common`; day 15 passes `(index := …)` to `distances` and its theorems; measured. Day 16's `Reindeer` index, if Matt wants it now. | Sonnet | 30-45 min |
| 3, later | `breadthFirst` over the same table (days 9, 18, 20), with the same optional argument; one table for `settled` and `best` (Lean's stale test); the queue generalised too, for `Std.Heap` and packed `Nat` keys via decoding (E3 to E1, 28% more on day 15). Each after a measurement. | Opus / Sonnet | not estimated |

Stages 1-2b: about **2.5-3.5 lane-hours** **[estimated from SW-2370's
12-minute re-proof of the same file and SW-2382's 30 minutes, padded for
the larger scope]**. Expected result: day 15 native about 3.0 s to about
1.45 s **[estimated, §1.1]**, every existing statement unchanged in
meaning, one new optional argument on `distances` and its two theorems,
and two new public names (`Graph.Costs`, `Graph.Index`) with their
instances.
