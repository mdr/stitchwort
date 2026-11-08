# Proposal: Dijkstra over an array, for states with a dense index

**Status:** draft 1, 8 November 2026. Ticket SW-2377 (paper lane, Opus).
Nothing is built or run for this note: the numbers are taken from
[SW-2369](../reviews/SW-2369-dijkstra-disk.md),
[SW-2371](../reviews/SW-2371-map-rebuild-reuse.md) and the SW-2370 and
SW-2382 lane reports on the board, and are marked **[measured]** (with
where) or **[estimated]** (with how). Code is as of `ca232293a`:
`crates/elab/src/std/Graph/Search.sw` after SW-2370 (improvement-only
pushes with a `best` map), SW-2382 (`searchFrom` takes the popped pair) and
SW-2376 (`reachable` by breadth-first search). Open questions Q1-Q4 are in
[§8](#8-open-questions); the orchestrator gives them D numbers.

## 0. Summary

- **The problem.** 2021 day 15 runs std's verified `Graph.distances` over
  260,000 grid positions. Its cost tables (`settled`, `best`) are tree
  `Map`s keyed by `Position`. With tonight's fixes it is about 3.0 s native
  against CPython's 0.5 s and Lean's 0.2 s. SW-2369 measured the same search
  by hand with the costs in an `Array` at **half the time** of the
  `Map` version (2.47 s to 1.19 s, same loaded machine).
- **The change.** Make the search generic over a small, lawful **cost
  table** (`Graph.Costs`: `empty`, `get`, `set` and three laws), so one
  proof covers every table. Then add a table for states with an index into
  `Fin n` (an `Array (Option Nat)`), and `Graph.distancesIndexed graph index
  sources`, which returns an ordinary `Map` and is **proved equal to
  `graph.distances sources`**. Callers' proofs carry over with one rewrite.
- **What it should do.** Day 15 from about 3.0 s to about 1.4-1.5 s
  native **[estimated]**, about 3x CPython rather than 6x; nothing else
  changes speed. The caller proves one fact about its index (decoding it
  gives the state back), which for a grid is a `Nat` division lemma std
  already has and its remainder partner.
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

**Public statements stay put.** `Bound`, `SearchResult` and `Shortest` are
stated about a `Map`; they become one-line wrappers over `…By` forms that
take a lookup function (`SearchResult graph sources reach result :=
SearchResultBy graph sources reach result.get`), so they unfold to what
they say now and `distancesCorrect`, `distancesShortest`, `boundAlong`,
`reachableIff` and the AoC proofs check unchanged. Whether the `…By` forms
are public is Q3's business; nothing outside `Search.sw` needs them if the
result is a `Map` ([§5](#5-the-result-a-map-built-at-the-end)).

**Run-time cost of the generality.** `costs.get` is a call through a record
field, as `Ord`'s `compare` already is; about 2 M such calls on day 15, a
few tens of milliseconds at the closure-call costs SW-2369 measured (14.5 M
`sw_apply_cached` in 5.3% of 5.5 s) **[estimated]**. Stage 1 checks that
`distances` doesn't regress beyond noise.

## 4. The index and the indexed table

### 4.1 What the caller gives

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
  condition on every law and into `SearchState`; Q4 asks.

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

`get` reads `cells` at `toFin state` (or `rest` when `None`); `set` writes
there. `sized` is what makes `getSet` hold for every table (`Array.getSet`
needs the index below the size; `Array.sizeSet` keeps it); it is a proof
field, so it is erased at run time (erase-proof-data.md, "The problem, plainly"). The laws
come from `Array.getSet`, `Array.getSetOther` (two different numbers, by
`roundTrip`), and the `Map` laws for `rest`.

### 4.3 The search

```stitchwort
--| `graph.distances sources`, with the search's cost tables kept in arrays
--| of `n` cells, one per state `index` numbers: for graphs such as grids
--| whose states are numbered densely. States `index` doesn't number still
--| work, kept in a map. [`Graph.distancesIndexedEq`] says it is `distances`.
def Graph.distancesIndexed [auto ord: Ord s] (graph: Graph s) (index: Index s n) (sources: List (s, Nat)): Map s Nat

theorem Graph.distancesIndexedEq [auto ord: Ord s] (graph: Graph s) (index: Index s n) (sources: List (s, Nat)):
    graph.distancesIndexed index sources = graph.distances sources
```

Day 15 becomes `risks.graph.distancesIndexed (Position.boxIndex
risks.height risks.width) [(risks.start, 0)]`, and its proofs start with
`rewrite Graph.distancesIndexedEq`.

## 5. The result: a `Map` built at the end

The search finishes with the settled table; `distancesIndexed` turns it
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

**Why it equals `distances`.** Two maps that both satisfy `Graph.Shortest`
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

That equality is why option B doesn't need a second public spec: every
theorem about `distances` is a theorem about `distancesIndexed`.

## 6. Python and Lean

| | Python (`main.py`) | Lean (`Dijkstra.lean`) | Stitchwort, this note |
|---|---|---|---|
| Costs so far | `dict` keyed by `(row, column)` | `Array Nat` of `size`, `∞` = 2^60, `set!` | `Array (Option Nat)` of `height * width` (`best`), and another (`settled`) |
| Stale pop | `risk > cost[(row, column)]` | `cost > distance[here]!` | `settled` cell is `Some` |
| Queue | `heapq` of `(risk, row, column)` | `TreeSet Nat`, key `distance * size + position` | `Set (Nat, Position)`, unchanged |
| Index | none (hashing) | `row * width + column`, unchecked | `Position.boxIndex`, with `roundTrip` proved |
| Proved | nothing | nothing (`!` reads panic out of range) | `distancesIndexed = distances`, so every shortest-path theorem |
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

Matt's, since they fix public API and names. The first is the one the next
lane needs.

- **Q1. Should std offer an array-backed Dijkstra, and how?** (a) one search
  over a cost table, with `distancesIndexed` proved equal to `distances`
  (option B) / (b) a separate copy (A) / (c) in `Aoc.Common` (C) / (d) not
  now (D). **[rec: (a).** One proof for both tables, no second spec for
  callers, and the gain (2x on day 15, measured by hand) is the largest
  left in the search.**]**
- **Q2. Its name.** `Graph.distancesIndexed graph index sources` /
  `Graph.distancesDense` / `Graph.distancesBy`. **[rec:
  `distancesIndexed`.** It says what the caller passes (an index); "dense"
  is the reason to use it, which the doc can say, and `By` suggests a key
  function.**]**
- **Q3. Its result.** (a) a `Map s Nat`, built at the end, equal to
  `distances` / (b) a view type over the array with `get` and `toMap`.
  **[rec: (a).** A drop-in with every `Map` lemma; about 0.05-0.1 s on day
  15 **[estimated]**; add (b) only if a measurement shows the build
  matters.**]**
- **Q4. The index.** (a) `Index s n` with `toFin`, `fromFin` and
  `roundTrip`, as a std type of its own (it isn't graph-specific: a dense
  set or table can use it), states without a number kept in a side map /
  (b) a bare `s → Option (Fin n)` with an injectivity proof / (c) as (a),
  but every state the search can reach must have a number (a coverage
  proof instead of the side map). **[rec: (a).** One obligation, proved by
  computation for grids; `fromFin` also lists the result in order and
  enables packed queue keys; no coverage proof.**]** The grid instance
  `Position.boxIndex` goes in `Aoc.Common` with `Position`; it moves to std
  if a std `Grid` arrives (arrays.md Q8).

## 9. Plan and estimate

| Stage | Work | Who | Estimate |
|---|---|---|---|
| 1 | `Graph.Costs` and its five consequences; the Dijkstra half of `Search.sw` generalised; `Graph.mapCosts`; `distances` at it; `…By` wrappers. Public statements unchanged; `bench:compare` dijkstra within noise; `audit:touched -- Std.Graph`. | Opus | 60-90 min |
| 2 | `Index`, `Graph.IndexedCosts`, `Graph.indexedCosts`, `distancesIndexed`, `shortestUnique`, `distancesIndexedEq`; zero array copies on day 15 (or stop: SW-2388 first). | Opus | 60-90 min |
| 2b | `Position.boxIndex` with `roundTrip` in `Aoc.Common`; day 15 switched, its proofs rewritten through `distancesIndexedEq`; measured. Day 16's `Reindeer` index, if Matt wants it now. | Sonnet | 30-45 min |
| 3, later | `breadthFirst` over the same table (days 9, 18, 20); one table for `settled` and `best` (Lean's stale test); the queue generalised too, for `Std.Heap` and packed `Nat` keys via `fromFin` (E3 to E1, 28% more on day 15). Each after a measurement. | Opus / Sonnet | not estimated |

Stages 1-2b: about **2.5-3.5 lane-hours** **[estimated from SW-2370's
12-minute re-proof of the same file and SW-2382's 30 minutes, padded for
the larger scope]**. Expected result: day 15 native about 3.0 s to about
1.45 s **[estimated, §1.1]**, every existing statement unchanged, two new
public theorems (`shortestUnique`, `distancesIndexedEq`) and two new
public names (`Index`, `distancesIndexed`).
