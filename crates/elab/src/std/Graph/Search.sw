--| Shortest paths in a graph given by each state's edges and their costs:
--| Dijkstra's algorithm (`Graph.distances`), and breadth-first search with a
--| plain queue for graphs whose edges each cost 1 (`Graph.breadthFirst`).
--|
--| Both are proved against one spec, `Graph.SearchResult`: each state found
--| is reached for its cost, by whatever notion of reaching the caller gives,
--| each source is found for no more than its starting cost, and each edge
--| out of a found state leads to one found for no more than the two costs
--| together. With reaching taken as walking the graph's edges from a source
--| (`Graph.Reached`), that is `Graph.Shortest`: each cost found is a walk's,
--| and no walk costs less ([`Graph.distancesShortest`],
--| [`Graph.breadthFirstShortest`]). [`Graph.boundAlong`] turns the spec into
--| bounds along any walk, for proofs about a program's own paths.
--|
--| [`Graph.fromEdges`] builds a graph from an edge function and a list of
--| states with nothing to prove, and [`Graph.reachable`] returns the states
--| reachable from some sources, whatever the edges cost.
--|
--| Both searches end without fuel because every edge leads to one of the
--| graph's listed `states`: each step settles one more of them, or shrinks
--| the queue.

--| A graph for a shortest-path search: each state's edges, with their costs,
--| and a list of states that every edge leads to.
type Graph (s: Type) = {
  edges: s → List (s, Nat),
  states: List s,
  listed: ∀ (state next: s) (weight: Nat) => (next, weight) ∈ edges state → next ∈ states
}

--| Builds a graph from `edges` and a list of `states`, keeping only the edges
--| whose target is on `states`, so nothing needs proving: every kept edge
--| leads to a listed state by construction. A state the list leaves out is
--| still searchable as a source, but no edge leads into it; to keep every
--| edge, list every state an edge can lead to; [`Graph.fromEdgesEdge`] says
--| exactly which edges stay. Each lookup of a state's edges filters
--| `edges state` against a set of `states` built once.
def Graph.fromEdges [auto ord: Ord s] (edges: s → List (s, Nat)) (states: List s): Graph s :=
  let known := Set.fromList states
  {
    edges = state => (edges state).filter (edge => known.contains edge.fst),
    states,
    listed = state next weight edge =>
      (Set.containsFromListIff states next).forward (And.right (List.memFilter _ _ edge))
  }

--| The edges of `Graph.fromEdges edges states` out of a state are those of
--| `edges` that lead to a listed state.
theorem Graph.fromEdgesEdge [auto ord: Ord s] (edges: s → List (s, Nat)) (states: List s) (state: s) (next: s) (weight: Nat):
    ((next, weight) ∈ (Graph.fromEdges edges states).edges state) ↔ (((next, weight) ∈ edges state) ∧ (next ∈ states)) := {
  forward = edge =>
    let (Both inEdges kept) := List.memFilter _ _ edge
    Both inEdges ((Set.containsFromListIff states next).forward kept),
  backward = (Both inEdges listed) =>
    List.memFilterIntro (edges state) _ inEdges ((Set.containsFromListIff states next).backward listed)
}

-- Walks

--| Edges followed from `start`, each one of the edges of the state before
--| it, ending at `finish`.
def Graph.Walk (graph: Graph s) (start: s): (steps: List (s, Nat)) → (finish: s) → Prop
  | [], finish => start = finish
  | [(next, weight), ..rest], finish => ((next, weight) ∈ graph.edges start) ∧ (graph.Walk next rest finish)

--| What a walk's edges cost together.
def Graph.cost (path: List (s, Nat)): Nat := path.sumBy Pair.snd

theorem Graph.costNil: Graph.cost ([]: List (s, Nat)) = 0 := rfl

theorem Graph.costCons (next: s) (weight: Nat) (rest: List (s, Nat)): Graph.cost [(next, weight), ..rest] = weight + Graph.cost rest :=
  List.sumByCons rest (next, weight) Pair.snd

theorem Graph.costAppend (path: List (s, Nat)) (more: List (s, Nat)): Graph.cost (path ++ more) = Graph.cost path + Graph.cost more :=
  List.sumByAppend path more Pair.snd

--| A walk, then another from where it ends.
theorem Graph.walkAppend (graph: Graph s) (more: List (s, Nat)) (finish: s) (start: s) (path: List (s, Nat)) (middle: s)
    (walked: graph.Walk start path middle) (after: graph.Walk middle more finish): graph.Walk start (path ++ more) finish :=
  match path, walked with
    | [], walked => rewrite walked in after
    | [(next, weight), ..rest], (Both edge later) => Both edge (Graph.walkAppend graph more finish next rest middle later after)

--| A walk, then one more edge.
theorem Graph.walkSnoc (graph: Graph s) (start: s) (path: List (s, Nat)) (middle: s) (walked: graph.Walk start path middle) (next: s) (weight: Nat)
    (edge: (next, weight) ∈ graph.edges middle): graph.Walk start (path ++ [(next, weight)]) next :=
  Graph.walkAppend graph [(next, weight)] next start path middle walked (Both edge rfl)

--| Some walk from a source ends at `state`, costing `cost` with the
--| source's starting cost.
def Graph.Reached (graph: Graph s) (sources: List (s, Nat)) (state: s) (cost: Nat): Prop :=
  Exists s (source =>
    Exists Nat (start =>
      Exists (List (s, Nat)) (path => ((source, start) ∈ sources) ∧ ((graph.Walk source path state) ∧ (start + Graph.cost path = cost)))))

theorem Graph.reachedSources (graph: Graph s) (sources: List (s, Nat)) (source: s) (start: Nat) (member: (source, start) ∈ sources):
    graph.Reached sources source start :=
  Witness source (Witness start (Witness [] (Both member (Both rfl (omega: start + 0 = start)))))

theorem Graph.reachedEdges (graph: Graph s) (sources: List (s, Nat)) (state: s) (cost: Nat) (reached: graph.Reached sources state cost)
    (next: s) (weight: Nat) (edge: (next, weight) ∈ graph.edges state): graph.Reached sources next (cost + weight) :=
  Exists.elim reached (source rest =>
    Exists.elim rest (start rest2 =>
      Exists.elim rest2 (path parts =>
        let (Both member (Both walked costs)) := parts
        Witness source
          (Witness start
            (Witness (path ++ [(next, weight)])
              (Both member
                (Both (Graph.walkSnoc graph source path state walked next weight edge)
                  (rewrite Graph.costAppend path [(next, weight)], Graph.costCons next weight [], Graph.costNil [s := s] in omega [costs]))))))))

-- The spec

--| `state` is settled for no more than `cost`.
def Graph.Bound [auto ord: Ord s] (settled: Map s Nat) (cost: Nat) (state: s): Prop :=
  Exists Nat (found => (settled.get state = Some found) ∧ (found ≤ cost))

--| A bound still holds for a larger cost.
theorem Graph.boundWeaken [auto ord: Ord s] (settled: Map s Nat) (cost: Nat) (more: Nat) (state: s) (bound: Graph.Bound settled cost state)
    (le: cost ≤ more): Graph.Bound settled more state :=
  Exists.elim bound (found both => Witness found (Both (And.left both) (omega [And.right both, le])))

--| What a search returns, for a `reach` that holds at the sources and along every edge.
--| Each settled state is reached for its cost, each source is settled for no
--| more than its starting cost, and each edge out of a settled state leads to
--| one settled for no more than the two together.
def Graph.SearchResult [auto ord: Ord s] (graph: Graph s) (sources: List (s, Nat)) (reach: s → Nat → Prop) (result: Map s Nat): Prop :=
  (∀ (state: s) (cost: Nat) => result.get state = Some cost → reach state cost) ∧ ((∀ (source: s) (start: Nat) => (source, start) ∈ sources → Graph.Bound result start source) ∧ (∀ (state: s) (cost: Nat) => result.get state = Some cost → ∀ (next: s) (weight: Nat) => (next, weight) ∈ graph.edges state →
    Graph.Bound result (cost + weight) next))

--| Along any walk, a search's bound grows by no more than the walk's cost.
theorem Graph.boundAlong [auto ord: Ord s] (graph: Graph s) (result: Map s Nat)
    (closed: ∀ (state: s) (cost: Nat) => result.get state = Some cost → ∀ (next: s) (weight: Nat) => (next, weight) ∈ graph.edges state →
      Graph.Bound result (cost + weight) next):
    ∀ (start: s) (cost: Nat) => Graph.Bound result cost start → ∀ (path: List (s, Nat)) (finish: s) => graph.Walk start path finish →
      Graph.Bound result (cost + Graph.cost path) finish
  | start, cost, bound, [], finish, walked => rewrite <- walked in Graph.boundWeaken result cost (cost + Graph.cost ([]: List (s, Nat))) start bound (omega)
  | start, cost, bound, [(next, weight), ..rest], finish, (Both edge later) =>
    Exists.elim bound (found both =>
      let stepped := closed start found (And.left both) next weight edge
      let along := Graph.boundAlong graph result closed next (cost + weight)
        (Graph.boundWeaken result (found + weight) (cost + weight) next stepped (omega [And.right both])) rest finish later
      Graph.boundWeaken result (cost + weight + Graph.cost rest) (cost + Graph.cost [(next, weight), ..rest]) finish along
        (rewrite Graph.costCons next weight rest in omega))

--| Each cost found is a walk's from a source, and no walk from a source
--| costs less.
def Graph.Shortest [auto ord: Ord s] (graph: Graph s) (sources: List (s, Nat)) (result: Map s Nat): Prop :=
  (∀ (state: s) (cost: Nat) => result.get state = Some cost → graph.Reached sources state cost) ∧ (∀ (source: s) (start: Nat) => (source, start) ∈ sources → ∀ (path: List (s, Nat)) (state: s) => graph.Walk source path state →
    Graph.Bound result (start + Graph.cost path) state)

theorem Graph.shortestOfResult [auto ord: Ord s] (graph: Graph s) (sources: List (s, Nat)) (result: Map s Nat)
    (correct: Graph.SearchResult graph sources (graph.Reached sources) result): Graph.Shortest graph sources result :=
  let (Both reachedAll (Both sourcesBound closed)) := correct
  Both reachedAll
    (source start member path state walked => Graph.boundAlong graph result closed source start (sourcesBound source start member) path state walked)

--| The states of `universe` not settled yet.
def Graph.unsettledIn [auto ord: Ord s] (universe: List s) (settled: Map s Nat): Nat := universe.count (state => !settled.contains state)

--| Settling more, including a state of `universe` not settled before,
--| leaves fewer unsettled.
theorem Graph.unsettledFewer [auto ord: Ord s] (universe: List s) (settled: Map s Nat) (more: Map s Nat)
    (grows: ∀ (state: s) => settled.contains state = True → more.contains state = True) (state: s) (member: state ∈ universe)
    (fresh: settled.contains state = False) (now: more.contains state = True): Graph.unsettledIn universe more < Graph.unsettledIn universe settled :=
  List.countLtMem universe (other => !more.contains other) (other => !settled.contains other)
    (other inside kept =>
      match there: settled.contains other with
        | True => rewrite grows other there at kept in kept
        | False => rfl)
    state member (rewrite fresh in rfl) (rewrite now in rfl)

-- Cost tables

--| A table of costs by state, of type `t`: how Dijkstra's search keeps the
--| least cost settled for each state and the least each has been queued
--| at. `get` is the cost the table has for a state, if any; `set` gives a
--| state a cost, replacing any it had. The three laws are all the search's
--| proof uses, so any table that keeps them will do: [`Graph.mapCosts`]
--| keeps the costs in a `Map`.
type Graph.Costs (s: Type) (t: Type) = {
  empty: t,
  get: t → s → Option Nat,
  set: t → s → Nat → t,
  --| The empty table has no cost for any state.
  getEmpty: ∀ (state: s) => get empty state = None,
  --| A state has the cost it was last set to.
  getSet: ∀ (table: t) (state: s) (cost: Nat) => get (set table state cost) state = Some cost,
  --| Setting one state's cost leaves every other state's as it was.
  getSetOther: ∀ (table: t) (state: s) (cost: Nat) (other: s) => other ≠ state → get (set table state cost) other = get table other
}

--| Costs kept in a `Map`: `get` is `Map.get` and `set` is `Map.insert`.
def Graph.mapCosts [auto ord: Ord s]: Graph.Costs s (Map s Nat) := {
  empty = Map.empty,
  get = table state => table.get state,
  set = table state cost => table.insert state cost,
  getEmpty = state => Map.getEmpty state,
  getSet = table state cost => Map.getInsert state cost table,
  getSetOther = table state cost other apart => Map.getInsertOther state cost other apart table
}

--| Whether the table has a cost for `state`.
def Graph.Costs.has (costs: Graph.Costs s t) (table: t) (state: s): Bool :=
  match costs.get table state with
    | Some _ => True
    | None => False

--| A state with a cost is one the table has.
theorem Graph.Costs.hasOfGet (costs: Graph.Costs s t) [table: t] [state: s] [cost: Nat] (got: costs.get table state = Some cost):
    costs.has table state = True :=
  rewrite got in rfl

--| A state the table has has some cost.
theorem Graph.Costs.getOfHas (costs: Graph.Costs s t) [table: t] [state: s] (there: costs.has table state = True):
    ∃ (cost: Nat) => costs.get table state = Some cost :=
  match got: costs.get table state with
    | Some cost => Witness cost rfl

--| A state just set is one the table has.
theorem Graph.Costs.hasSetSame (costs: Graph.Costs s t) (table: t) (state: s) (cost: Nat): costs.has (costs.set table state cost) state = True :=
  costs.hasOfGet (costs.getSet table state cost)

--| Setting a state's cost keeps every state the table had.
theorem Graph.Costs.hasSetKeeps [auto ord: Ord s] (costs: Graph.Costs s t) (table: t) (state: s) (cost: Nat) [other: s]
    (there: costs.has table other = True): costs.has (costs.set table state cost) other = True :=
  match same: other == state with
    | True => rewrite DecEq.sound same in costs.hasSetSame table state cost
    | False => rewrite costs.getSetOther table state cost other (DecEq.soundFalse other state same) in there

--| After setting a state's cost, a state has either that cost, being the
--| state set, or what it had before.
theorem Graph.Costs.getSetCases [auto ord: Ord s] (costs: Graph.Costs s t) [table: t] [state: s] [cost: Nat] [other: s] [found: Nat]
    (there: costs.get (costs.set table state cost) other = Some found): ((other = state) ∧ (found = cost)) ∨ (costs.get table other = Some found) :=
  match same: other == state with
    | True =>
      let equal := DecEq.sound same
      Inl (Both equal (Option.someInjective (Eq.trans (Eq.sym there) (rewrite equal in costs.getSet table state cost))))
    | False => Inr (Eq.trans (Eq.sym (costs.getSetOther table state cost other (DecEq.soundFalse other state same))) there)

--| Setting the cost of a state the table doesn't have keeps every cost it
--| has.
theorem Graph.Costs.getSetKeeps [auto ord: Ord s] (costs: Graph.Costs s t) (table: t) (state: s) (cost: Nat) (fresh: costs.has table state = False)
    [other: s] [found: Nat] (there: costs.get table other = Some found): costs.get (costs.set table state cost) other = Some found :=
  match same: other == state with
    | True =>
      let equal := DecEq.sound same
      Void.exfalso (Bool.falseNotTrue (Eq.trans (Eq.sym fresh) (rewrite <- equal in costs.hasOfGet there)))
    | False => Eq.trans (costs.getSetOther table state cost other (DecEq.soundFalse other state same)) there

-- Numbered states

--| Numbers some states from `0` to `size - 1`, each with its own number, so
--| that a search can keep their costs in an array: `graph.distances (index
--| := grid.index) sources`. `decode` gives a state's number back as the
--| state. States without a number are allowed; their costs are kept in a
--| map. The two proofs are erased at run time, so an index is its size and
--| two functions.
type Graph.Index (s: Type) = {
  size: Nat,
  number: s → Option Nat,
  decode: Nat → Option s,
  --| Every number is below `size`.
  below: ∀ (state: s) (i: Nat) => number state = Some i → i < size,
  --| Decoding a state's number gives the state back.
  roundTrip: ∀ (state: s) (i: Nat) => number state = Some i → decode i = Some state
}

--| The index that numbers no state, and so has size 0: [`Graph.distances`]
--| without an index keeps its costs in maps.
def Graph.Index.none: Graph.Index s := {
  size = 0,
  number = _ => None,
  decode = _ => None,
  below = state i numbered => Void.exfalso (Option.noneNotSome i numbered),
  roundTrip = state i numbered => Void.exfalso (Option.noneNotSome i numbered)
}

--| Two states with the same number are the same state.
theorem Graph.Index.sameNumber (index: Graph.Index s) [a: s] [b: s] [i: Nat] (numberA: index.number a = Some i) (numberB: index.number b = Some i):
    a = b :=
  Option.someInjective (Eq.trans (Eq.sym (index.roundTrip a i numberA)) (index.roundTrip b i numberB))

--| Costs by state for [`Graph.indexCosts`]: a cell for each number below
--| the index's size, holding the cost of the state with that number if it
--| has one, and a map for the states without a number. The proofs are
--| erased at run time.
type Graph.IndexTable (s: Type) (index: Graph.Index s) [auto ord: Ord s] = {
  cells: Array (Option Nat),
  rest: Map s Nat,
  --| There is a cell for every number.
  sized: cells.size = index.size,
  --| A cell with a cost belongs to the state its number decodes to.
  numbered: ∀ (i cost: Nat) (state: s) => cells.getOr i None = Some cost → index.decode i = Some state → index.number state = Some i,
  --| The map has only states without a number.
  unnumbered: ∀ (state: s) => rest.contains state = True → index.number state = None
}

--| The table with no costs.
def Graph.IndexTable.empty [auto ord: Ord s] (index: Graph.Index s): Graph.IndexTable s index := {
  cells = Array.replicate index.size None,
  rest = Map.empty,
  sized = Array.sizeReplicate index.size None,
  numbered = i cost state there decoded => Void.exfalso (Option.noneNotSome cost (rewrite Array.getOrReplicate index.size None i at there in there)),
  unnumbered = state there => cases
}

--| The cost the table has for `state`: its cell's, or the map's for a state
--| without a number.
@[noReceiver]
def Graph.IndexTable.get [auto ord: Ord s] (index: Graph.Index s) (table: Graph.IndexTable s index) (state: s): Option Nat :=
  match index.number state with
    | Some i => table.cells.getOr i None
    | None => table.rest.get state

--| Setting a numbered state's cell keeps every cell with a cost belonging
--| to its state.
theorem Graph.IndexTable.setNumbered (index: Graph.Index s) (cells: Array (Option Nat))
    (kept: ∀ (i cost: Nat) (state: s) => cells.getOr i None = Some cost → index.decode i = Some state → index.number state = Some i)
    (state: s) (cost: Nat) (i: Nat) (numbered: index.number state = Some i) (j: Nat) (found: Nat) (other: s)
    (there: (cells.set i (Some cost)).getOr j None = Some found) (decoded: index.decode j = Some other): index.number other = Some j :=
  if same: j = i then
    let isState: other = state := Option.someInjective (Eq.trans (Eq.sym decoded) (rewrite same in index.roundTrip state i numbered))
    rewrite isState, same in numbered
  else kept j found other (rewrite Array.getOrSetOther cells i (Some cost) j None same at there in there) decoded

--| Putting a state without a number in the map keeps the map to such
--| states.
theorem Graph.IndexTable.insertUnnumbered [auto ord: Ord s] (index: Graph.Index s) (rest: Map s Nat)
    (kept: ∀ (state: s) => rest.contains state = True → index.number state = None) (state: s) (cost: Nat)
    (unnumbered: index.number state = None) (other: s) (there: (rest.insert state cost).contains other = True): index.number other = None :=
  match same: other == state with
    | True => rewrite DecEq.sound same in unnumbered
    | False => kept other (rewrite Map.getInsertOther state cost other (DecEq.soundFalse other state same) rest at there in there)

--| The table with `state` given `cost`. The array is changed in place when
--| nothing else holds the table.
@[noReceiver]
def Graph.IndexTable.set [auto ord: Ord s] (index: Graph.Index s) (table: Graph.IndexTable s index) (state: s) (cost: Nat): Graph.IndexTable s index :=
  Graph.IndexTable.setAt index table state cost (index.number state) rfl

--| `set`, given the state's number.
@[noReceiver]
def Graph.IndexTable.setAt [auto ord: Ord s] (index: Graph.Index s) (table: Graph.IndexTable s index) (state: s) (cost: Nat):
    (number: Option Nat) → index.number state = number → Graph.IndexTable s index
  | Some i, numbered =>
    -- Taken apart rather than projected, so that the array is moved out of
    -- the table and changed in place: projecting `cells` and then `rest`
    -- would leave the table holding the array while `set` runs.
    match table with
      | { cells, rest, sized, numbered = kept, unnumbered } => {
          cells = cells.set i (Some cost),
          rest,
          sized = rewrite Array.sizeSet cells i (Some cost) in sized,
          numbered = Graph.IndexTable.setNumbered index cells kept state cost i numbered,
          unnumbered
        }
  | None, numbered =>
    match table with
      | { cells, rest, sized, numbered = kept, unnumbered = restKept } => {
        cells,
        rest = rest.insert state cost,
        sized,
        numbered = kept,
        unnumbered = Graph.IndexTable.insertUnnumbered index rest restKept state cost numbered
      }

--| A state has the cost it was last set to.
theorem Graph.IndexTable.getSetAt [auto ord: Ord s] (index: Graph.Index s) (table: Graph.IndexTable s index) (state: s) (cost: Nat)
    (number: Option Nat) (numbered: index.number state = number):
    Graph.IndexTable.get index (Graph.IndexTable.setAt index table state cost number numbered) state = Some cost :=
  match number with
    | Some i => rewrite numbered in Array.getOrSet table.cells i (Some cost) None (rewrite table.sized in index.below state i numbered)
    | None => rewrite numbered in Map.getInsert state cost table.rest

--| Setting one state's cost leaves every other state's as it was.
theorem Graph.IndexTable.getSetAtOther [auto ord: Ord s] (index: Graph.Index s) (table: Graph.IndexTable s index) (state: s) (cost: Nat)
    (other: s) (apart: other ≠ state) (number: Option Nat) (numbered: index.number state = number):
    Graph.IndexTable.get index (Graph.IndexTable.setAt index table state cost number numbered) other = Graph.IndexTable.get index table other :=
  match number with
    | Some i =>
      match otherNumbered: index.number other with
        | Some j =>
          Array.getOrSetOther table.cells i (Some cost) j None
            (same => apart (Graph.Index.sameNumber index otherNumbered (rewrite <- same at numbered in numbered)))
        | None => rfl
    | None =>
      match otherNumbered: index.number other with
        | Some j => rfl
        | None => Map.getInsertOther state cost other apart table.rest

--| Costs kept by number in an array, for the states `index` numbers, and in
--| a `Map` for the rest: what [`Graph.distances`] uses when given an index.
def Graph.indexCosts [auto ord: Ord s] (index: Graph.Index s): Graph.Costs s (Graph.IndexTable s index) := {
  empty = Graph.IndexTable.empty index,
  get = table state => Graph.IndexTable.get index table state,
  set = table state cost => Graph.IndexTable.set index table state cost,
  getEmpty = state =>
    match numbered: index.number state with
      | Some i => Array.getOrReplicate index.size None i
      | None => Map.getEmpty state,
  getSet = table state cost => Graph.IndexTable.getSetAt index table state cost (index.number state) rfl,
  getSetOther = table state cost other apart => Graph.IndexTable.getSetAtOther index table state cost other apart (index.number state) rfl
}

--| Cell `j` of the cells after the one numbered `start` is numbered
--| `start + Succ j`.
theorem Graph.Index.shift (start: Nat) (j: Nat): start + 1 + j = start + Succ j := omega

--| The state and cost of each cell with a cost, numbering the cells from
--| `start`, in order.
def Graph.Index.entries (index: Graph.Index s): (start: Nat) → (cells: List (Option Nat)) → List (s, Nat)
  | start, [] => []
  | start, [None, ..rest] => index.entries (start + 1) rest
  | start, [Some cost, ..rest] =>
    match index.decode start with
      | Some state => [(state, cost), ..index.entries (start + 1) rest]
      | None => index.entries (start + 1) rest

--| The entries have no pair for a state whose number isn't a cell's, when
--| each cell with a cost belongs to the state its number decodes to.
theorem Graph.Index.lookupEntriesOff [auto ord: Ord s] (index: Graph.Index s) (state: s) (start: Nat) (cells: List (Option Nat))
    (numbered: (∀ (j cost: Nat) (other: s) => cells.getOr j None = Some cost → index.decode (start + j) = Some other → index.number other = Some (start + j)))
    (off: (∀ (j: Nat) => index.number state ≠ Some (start + j))): Map.lookupLast state (index.entries start cells) = None :=
  match cells with
    | [] => rfl
    | [None, ..rest] =>
      index.lookupEntriesOff state (start + 1) rest
        (j cost other there decoded => rewrite <- Graph.Index.shift start j in numbered (Succ j) cost other there (rewrite Graph.Index.shift start j at decoded in decoded))
        (j same => off (Succ j) (rewrite Graph.Index.shift start j at same in same))
    | [Some cost, ..rest] =>
      let tail :=
        index.lookupEntriesOff state (start + 1) rest
          (j found other there decoded =>
            rewrite <- Graph.Index.shift start j in numbered (Succ j) found other there (rewrite Graph.Index.shift start j at decoded in decoded))
          (j same => off (Succ j) (rewrite Graph.Index.shift start j at same in same))
      match decoded: index.decode start with
        | None => tail
        | Some other =>
          rewrite Map.lookupLastConsOther state other cost (index.entries (start + 1) rest)
            (same => off 0 (rewrite same in numbered 0 cost other rfl (rewrite Nat.addZero start in decoded))) in
            tail

--| The entries' pair for a state numbered `start + j` has the cost in cell
--| `j`, when each cell with a cost belongs to the state its number decodes
--| to.
theorem Graph.Index.lookupEntriesAt [auto ord: Ord s] (index: Graph.Index s) (state: s) (start: Nat) (cells: List (Option Nat)) (j: Nat)
    (numbered: (∀ (j cost: Nat) (other: s) => cells.getOr j None = Some cost → index.decode (start + j) = Some other → index.number other = Some (start + j)))
    (at: index.number state = Some (start + j)): Map.lookupLast state (index.entries start cells) = cells.getOr j None :=
  match cells, j with
    | [], j => rfl
    | [None, ..rest], Zero =>
      index.lookupEntriesOff state (start + 1) rest
        (j cost other there decoded => rewrite <- Graph.Index.shift start j in numbered (Succ j) cost other there (rewrite Graph.Index.shift start j at decoded in decoded))
        (k same => omega [Option.someInjective (Eq.trans (Eq.sym at) same)])
    | [Some cost, ..rest], Zero =>
      let atStart: index.number state = Some start := rewrite Nat.addZero start at at in at
      let tail :=
        index.lookupEntriesOff state (start + 1) rest
          (j found other there decoded =>
            rewrite <- Graph.Index.shift start j in numbered (Succ j) found other there (rewrite Graph.Index.shift start j at decoded in decoded))
          (k same => omega [Option.someInjective (Eq.trans (Eq.sym atStart) same)])
      rewrite index.roundTrip state start atStart in Map.lookupLastConsSame state cost (index.entries (start + 1) rest) tail
    | [None, ..rest], Succ k =>
      index.lookupEntriesAt state (start + 1) rest k
        (j cost other there decoded => rewrite <- Graph.Index.shift start j in numbered (Succ j) cost other there (rewrite Graph.Index.shift start j at decoded in decoded))
        (rewrite Graph.Index.shift start k in at)
    | [Some cost, ..rest], Succ k =>
      let tail :=
        index.lookupEntriesAt state (start + 1) rest k
          (j found other there decoded =>
            rewrite <- Graph.Index.shift start j in numbered (Succ j) found other there (rewrite Graph.Index.shift start j at decoded in decoded))
          (rewrite Graph.Index.shift start k in at)
      match decoded: index.decode start with
        | None => tail
        | Some other =>
          rewrite Map.lookupLastConsOther state other cost (index.entries (start + 1) rest)
            (same =>
              let otherAt := numbered 0 cost other rfl (rewrite Nat.addZero start in decoded)
              omega [Option.someInjective (Eq.trans (Eq.sym at) (rewrite <- same at otherAt in otherAt))]) in
            tail

--| The table as a map: the cells with a cost in order of their numbers,
--| with the states their numbers decode to, then the states without a
--| number. When the numbers follow the states' order, as a grid's do row by
--| row, the map is built in O(n).
@[noReceiver]
def Graph.IndexTable.toMap [auto ord: Ord s] (index: Graph.Index s) (table: Graph.IndexTable s index): Map s Nat :=
  Map.fromList (index.entries 0 table.cells.toList ++ table.rest.toList)

--| The map has what the table has.
theorem Graph.IndexTable.getToMap [auto ord: Ord s] (index: Graph.Index s) (table: Graph.IndexTable s index) (state: s):
    (Graph.IndexTable.toMap index table).get state = Graph.IndexTable.get index table state :=
  let entries := index.entries 0 table.cells.toList
  let restGot := Map.lookupLastToList table.rest state
  let cellsNumbered: ∀ (j cost: Nat) (other: s) => table.cells.toList.getOr j None = Some cost → index.decode (0 + j) = Some other →
      index.number other = Some (0 + j) :=
    j cost other there decoded => table.numbered j cost other there decoded
  rewrite Map.getFromList state (entries ++ table.rest.toList) in
    match numberedAs: index.number state with
      | None =>
        match got: table.rest.get state with
          | Some cost => Map.lookupLastAppendRight state table.rest.toList (Eq.trans restGot got) entries
          | None =>
            Eq.trans (Map.lookupLastAppendLeft state table.rest.toList (Eq.trans restGot got) entries)
              (index.lookupEntriesOff state 0 table.cells.toList cellsNumbered (j same => Option.noneNotSome (0 + j) (Eq.trans (Eq.sym numberedAs) same)))
      | Some i =>
        let restMissing: table.rest.get state = None :=
          match got: table.rest.get state with
            | None => rfl
            | Some cost =>
              Void.exfalso (Option.noneNotSome i (Eq.trans (Eq.sym (table.unnumbered state (Map.containsOfGet table.rest state cost got))) numberedAs))
        Eq.trans (Map.lookupLastAppendLeft state table.rest.toList (Eq.trans restGot restMissing) entries)
          (index.lookupEntriesAt state 0 table.cells.toList i cellsNumbered numberedAs)

-- Dijkstra's algorithm

--| `Graph.Bound` for costs read by `get`: `state` has a cost of no more
--| than `cost`.
def Graph.BoundBy (get: s → Option Nat) (cost: Nat) (state: s): Prop :=
  Exists Nat (found => (get state = Some found) ∧ (found ≤ cost))

--| A bound still holds for a larger cost.
theorem Graph.boundByWeaken (get: s → Option Nat) (cost: Nat) (more: Nat) (state: s) (bound: Graph.BoundBy get cost state)
    (le: cost ≤ more): Graph.BoundBy get more state :=
  Exists.elim bound (found both => Witness found (Both (And.left both) (omega [And.right both, le])))

--| `Graph.SearchResult` for a result read by `get`, as the search over any
--| cost table proves it. At [`Graph.mapCosts`] it is `SearchResult` itself.
def Graph.SearchResultBy (graph: Graph s) (sources: List (s, Nat)) (reach: s → Nat → Prop) (get: s → Option Nat): Prop :=
  (∀ (state: s) (cost: Nat) => get state = Some cost → reach state cost) ∧ ((∀ (source: s) (start: Nat) => (source, start) ∈ sources → Graph.BoundBy get start source) ∧ (∀ (state: s) (cost: Nat) => get state = Some cost → ∀ (next: s) (weight: Nat) => (next, weight) ∈ graph.edges state →
    Graph.BoundBy get (cost + weight) next))

--| The states of `universe` the table of settled costs doesn't have yet.
def Graph.unsettledAt (costs: Graph.Costs s t) (universe: List s) (settled: t): Nat := universe.count (state => !costs.has settled state)

--| Settling more, including a state of `universe` not settled before,
--| leaves fewer unsettled.
theorem Graph.unsettledAtFewer (costs: Graph.Costs s t) (universe: List s) (settled: t) (more: t)
    (grows: ∀ (state: s) => costs.has settled state = True → costs.has more state = True) (state: s) (member: state ∈ universe)
    (fresh: costs.has settled state = False) (now: costs.has more state = True): Graph.unsettledAt costs universe more < Graph.unsettledAt costs universe settled :=
  List.countLtMem universe (other => !costs.has more other) (other => !costs.has settled other)
    (other inside kept =>
      match there: costs.has settled other with
        | True => rewrite grows other there at kept in kept
        | False => rfl)
    state member (rewrite fresh in rfl) (rewrite now in rfl)

--| Whether `total` is less than the cost `best` has for `state`; it is
--| when `best` has none.
def Graph.improves (costs: Graph.Costs s t) (best: t) (state: s) (total: Nat): Bool :=
  match costs.get best state with
    | None => True
    | Some known => total < known

--| A cost that doesn't improve is no less than one `best` has.
theorem Graph.improvesFalse (costs: Graph.Costs s t) (best: t) (state: s) (total: Nat) (no: Graph.improves costs best state total = False):
    Exists Nat (known => (costs.get best state = Some known) ∧ (known ≤ total)) :=
  match got: costs.get best state with
    | Some known => Witness known (Both rfl omega)

--| A cost that improves is less than any `best` has.
theorem Graph.improvesTrue (costs: Graph.Costs s t) (best: t) (state: s) (total: Nat) (yes: Graph.improves costs best state total = True)
    (known: Nat) (got: costs.get best state = Some known): total < known :=
  rewrite got at yes in omega

--| Each edge whose state it gets to for less than `best` has, at `cost`
--| plus the edge's: the state queued at that cost, and the cost kept in
--| `best`. A settled state is never queued again: `best` has it for no more
--| than its settled cost, which no later cost is below.
@[tailrec]
def Graph.relaxEdges [auto ord: Ord s] (costs: Graph.Costs s t) (cost: Nat): (edges: List (s, Nat)) → (queue: Set (Nat, s)) → (best: t) → (Set (Nat, s), t)
  | [], queue, best => (queue, best)
  | [(next, weight), ..rest], queue, best =>
    if Graph.improves costs best next (cost + weight) then
      Graph.relaxEdges costs cost rest (queue.insert (cost + weight, next)) (costs.set best next (cost + weight))
    else Graph.relaxEdges costs cost rest queue best

--| Relaxing edges keeps what the queue had.
theorem Graph.relaxKeeps [auto ord: Ord s] (costs: Graph.Costs s t) (cost: Nat) (edges: List (s, Nat)) (queue: Set (Nat, s)) (best: t) (entry: (Nat, s))
    (there: queue.contains entry = True): (Graph.relaxEdges costs cost edges queue best).fst.contains entry = True :=
  match edges with
    | [] => there
    | [(next, weight), ..rest] =>
      match better: Graph.improves costs best next (cost + weight) with
        | True =>
          Graph.relaxKeeps costs cost rest (queue.insert (cost + weight, next)) (costs.set best next (cost + weight)) entry
            (Set.containsInsertMono queue (cost + weight, next) entry there)
        | False => Graph.relaxKeeps costs cost rest queue best entry there

--| Relaxing edges queues nothing but each edge's state at `cost` plus its
--| cost.
theorem Graph.relaxAdded [auto ord: Ord s] (costs: Graph.Costs s t) (cost: Nat) (edges: List (s, Nat)) (queue: Set (Nat, s)) (best: t) (total: Nat) (state: s)
    (there: (Graph.relaxEdges costs cost edges queue best).fst.contains (total, state) = True):
    (queue.contains (total, state) = True) ∨ (Exists Nat (weight => ((state, weight) ∈ edges) ∧ (total = cost + weight))) :=
  match edges with
    | [] => Inl there
    | [(next, weight), ..rest] =>
      match better: Graph.improves costs best next (cost + weight) with
        | False =>
          match Graph.relaxAdded costs cost rest queue best total state there with
            | Inl old => Inl old
            | Inr (Witness found (Both member costsEqual)) => Inr (Witness found (Both (Inr member) costsEqual))
        | True =>
          match Graph.relaxAdded costs cost rest (queue.insert (cost + weight, next)) (costs.set best next (cost + weight)) total state there with
            | Inr (Witness found (Both member costsEqual)) => Inr (Witness found (Both (Inr member) costsEqual))
            | Inl inserted =>
              match same: (total, state) == (cost + weight, next) with
                | True =>
                  let equal := DecEq.sound [x := (total, state)] [y := (cost + weight, next)] same
                  Inr (Witness weight (Both (Inl (Eq.cong (found => (found, weight)) (Eq.sym (Eq.cong Pair.snd equal)))) (Eq.cong Pair.fst equal)))
                | False =>
                  Inl (Eq.trans (Eq.sym (Set.containsInsertOther queue (cost + weight, next) (total, state) (DecEq.soundFalse _ _ same))) inserted)

--| Each cost relaxing edges records in `best` was there before, or is
--| queued.
theorem Graph.relaxBest [auto ord: Ord s] (costs: Graph.Costs s t) (cost: Nat) (edges: List (s, Nat)) (queue: Set (Nat, s)) (best: t) (state: s) (found: Nat)
    (got: costs.get (Graph.relaxEdges costs cost edges queue best).snd state = Some found):
    (costs.get best state = Some found) ∨ ((Graph.relaxEdges costs cost edges queue best).fst.contains (found, state) = True) :=
  match edges with
    | [] => Inl got
    | [(next, weight), ..rest] =>
      match better: Graph.improves costs best next (cost + weight) with
        | False => Graph.relaxBest costs cost rest queue best state found got
        | True =>
          let more := queue.insert (cost + weight, next)
          match Graph.relaxBest costs cost rest more (costs.set best next (cost + weight)) state found got with
            | Inr queued => Inr queued
            | Inl inserted =>
              match costs.getSetCases inserted with
                | Inr old => Inl old
                | Inl (Both same costsEqual) =>
                  Inr
                    (rewrite same, costsEqual in
                      Graph.relaxKeeps costs cost rest more (costs.set best next (cost + weight)) (cost + weight, next)
                        (Set.containsInsert (cost + weight, next) queue))

--| Relaxing edges never raises a cost `best` has.
theorem Graph.relaxLowers [auto ord: Ord s] (costs: Graph.Costs s t) (cost: Nat) (edges: List (s, Nat)) (queue: Set (Nat, s)) (best: t) (state: s) (known: Nat)
    (got: costs.get best state = Some known):
    Exists Nat (found => (costs.get (Graph.relaxEdges costs cost edges queue best).snd state = Some found) ∧ (found ≤ known)) :=
  match edges with
    | [] => Witness known (Both got (Nat.leRefl known))
    | [(next, weight), ..rest] =>
      match better: Graph.improves costs best next (cost + weight) with
        | False => Graph.relaxLowers costs cost rest queue best state known got
        | True =>
          let more := queue.insert (cost + weight, next)
          let lowered := costs.set best next (cost + weight)
          match same: state == next with
            | True =>
              let equal := DecEq.sound same
              let less := Graph.improvesTrue costs best next (cost + weight) better known (rewrite <- equal in got)
              let (Witness found (Both final le)) :=
                Graph.relaxLowers costs cost rest more lowered state (cost + weight) (rewrite equal in costs.getSet best next (cost + weight))
              Witness found (Both final (omega [le, less]))
            | False =>
              Graph.relaxLowers costs cost rest more lowered state known
                (Eq.trans (costs.getSetOther best next (cost + weight) state (DecEq.soundFalse _ _ same)) got)

--| After relaxing edges, `best` has each edge's state for no more than
--| `cost` plus the edge's.
theorem Graph.relaxCovers [auto ord: Ord s] (costs: Graph.Costs s t) (cost: Nat) (edges: List (s, Nat)) (queue: Set (Nat, s)) (best: t) (next: s) (weight: Nat)
    (member: (next, weight) ∈ edges):
    Exists Nat (found => (costs.get (Graph.relaxEdges costs cost edges queue best).snd next = Some found) ∧ (found ≤ cost + weight)) :=
  match edges, member with
    | [], member => Void.exfalso member
    | [(first, firstWeight), ..rest], Inr later =>
      match better: Graph.improves costs best first (cost + firstWeight) with
        | False => Graph.relaxCovers costs cost rest queue best next weight later
        | True =>
          Graph.relaxCovers costs cost rest (queue.insert (cost + firstWeight, first)) (costs.set best first (cost + firstWeight)) next weight later
    | [(first, firstWeight), ..rest], Inl here =>
      rewrite <- Eq.cong Pair.fst here, <- Eq.cong Pair.snd here in
        match better: Graph.improves costs best first (cost + firstWeight) with
          | False =>
            let (Witness known (Both got le)) := Graph.improvesFalse costs best first (cost + firstWeight) better
            let (Witness found (Both final lower)) := Graph.relaxLowers costs cost rest queue best first known got
            Witness found (Both final (omega [le, lower]))
          | True =>
            let (Witness found (Both final lower)) :=
              Graph.relaxLowers costs cost rest (queue.insert (cost + firstWeight, first)) (costs.set best first (cost + firstWeight)) first
                (cost + firstWeight) (costs.getSet best first (cost + firstWeight))
            Witness found (Both final lower)

--| `Less` then anything is never a first comparison of `Greater`.
theorem Graph.notGreaterOfThen: ∀ (first second: Ordering) => Ordering.andThen first second = Less → first ≠ Greater
  | Less, second, less, same => Ordering.lessNotGreater same
  | Equal, second, less, same => Ordering.equalNotGreater same
  | Greater, second, less, same => Ordering.greaterNotLess less

--| The least pair of a queue costs no more than any pair in it.
theorem Graph.minLeast [auto ord: Ord s] (queue: Set (Nat, s)) (cost: Nat) (state: s) (found: queue.min = Some (cost, state)) (other: Nat)
    (otherState: s) (there: queue.contains (other, otherState) = True): cost ≤ other :=
  match entries: Map.toList queue.items with
    | [] => Void.exfalso (Option.someNotNone (cost, state) (Eq.trans (Eq.sym found) (rewrite Map.minToList queue.items, entries in rfl)))
    | [(key, unit), ..rest] =>
      let first: queue.min = Some key := rewrite Map.minToList queue.items, entries in rfl
      let same: key = (cost, state) := Option.someInjective (Eq.trans (Eq.sym first) found)
      let member := Map.memKeysOfContains queue.items (other, otherState) there
      rewrite entries at member in
        match member with
          | Inl here => rewrite Eq.cong Pair.fst (Eq.trans (Eq.sym same) here) in Nat.leRefl other
          | Inr later =>
            let sorted := Map.toListSorted queue.items
            rewrite entries at sorted in
              let (Both bottom ascending) := sorted
              let above := Map.Spec.keysAbove _ (other, otherState) (Some key) rest ascending later
              rewrite same at above in Nat.leOfCompare cost other (Graph.notGreaterOfThen _ _ above)

--| What the search may settle: the sources' states and the listed ones.
def Graph.universe (graph: Graph s) (sources: List (s, Nat)): List s := sources.map Pair.fst ++ graph.states

--| Every state queued at the start is in the universe.
theorem Graph.startQueued [auto ord: Ord s] (graph: Graph s) (costs: Graph.Costs s t) (sources: List (s, Nat)) (cost: Nat) (state: s)
    (there: (Graph.relaxEdges costs 0 sources Set.empty costs.empty).fst.contains (cost, state) = True): state ∈ graph.universe sources :=
  match Graph.relaxAdded costs 0 sources Set.empty costs.empty cost state there with
    | Inl none => cases
    | Inr (Witness start (Both member costsEqual)) =>
      List.memAppendLeft state (sources.map Pair.fst) graph.states (List.memMap sources (state, start) member Pair.fst)

--| Every state queued after popping the least pair is in the universe.
theorem Graph.restQueued [auto ord: Ord s] (graph: Graph s) (sources: List (s, Nat)) (queue: Set (Nat, s)) (popped: (Nat, s))
    (rest: Set (Nat, s)) (found: queue.popMin = Some (popped, rest))
    (queued: ∀ (cost: Nat) (state: s) => queue.contains (cost, state) = True → state ∈ graph.universe sources) (cost: Nat) (state: s)
    (there: rest.contains (cost, state) = True): state ∈ graph.universe sources :=
  let (Both least restIs) := Set.popMinSome queue popped rest found
  queued cost state (Set.containsOfRemove queue popped (cost, state) (rewrite restIs at there in there))

--| Every state queued after relaxing a state's edges is in the universe.
theorem Graph.relaxedQueued [auto ord: Ord s] (graph: Graph s) (costs: Graph.Costs s t) (sources: List (s, Nat)) (from: s) (fromCost: Nat)
    (rest: Set (Nat, s)) (best: t) (queued: ∀ (cost: Nat) (state: s) => rest.contains (cost, state) = True → state ∈ graph.universe sources)
    (cost: Nat) (state: s) (there: (Graph.relaxEdges costs fromCost (graph.edges from) rest best).fst.contains (cost, state) = True):
    state ∈ graph.universe sources :=
  match Graph.relaxAdded costs fromCost (graph.edges from) rest best cost state there with
    | Inl inRest => queued cost state inRest
    | Inr (Witness weight (Both edge costsEqual)) =>
      List.memAppendRight state (sources.map Pair.fst) graph.states (graph.listed from state weight edge)

--| What the search knows about the queue it popped `popped` from, once it
--| no longer holds that queue: some queue pops as `popped`, and every state
--| on it is in the universe. Being a proposition, it costs nothing at run
--| time, so the search holds only the popped pair and the rest.
def Graph.Queued [auto ord: Ord s] (graph: Graph s) (sources: List (s, Nat)) (popped: Option ((Nat, s), Set (Nat, s))): Prop :=
  ∃ (queue: Set (Nat, s)) => (queue.popMin = popped) ∧ (∀ (cost: Nat) (state: s) => queue.contains (cost, state) = True → state ∈ graph.universe sources)

--| Popping a queue whose states are all in the universe.
theorem Graph.queuedPop [auto ord: Ord s] (graph: Graph s) (sources: List (s, Nat)) (queue: Set (Nat, s))
    (queued: ∀ (cost: Nat) (state: s) => queue.contains (cost, state) = True → state ∈ graph.universe sources): Graph.Queued graph sources queue.popMin :=
  Witness queue (Both rfl queued)

--| Every state left on the queue after popping is in the universe.
theorem Graph.queuedRest [auto ord: Ord s] (graph: Graph s) (sources: List (s, Nat)) (popped: (Nat, s)) (rest: Set (Nat, s))
    (queued: Graph.Queued graph sources (Some (popped, rest))) (cost: Nat) (state: s) (there: rest.contains (cost, state) = True):
    state ∈ graph.universe sources :=
  Exists.elim queued (queue facts => Graph.restQueued graph sources queue popped rest (And.left facts) (And.right facts) cost state there)

--| The popped state is in the universe.
theorem Graph.queuedLeast [auto ord: Ord s] (graph: Graph s) (sources: List (s, Nat)) (cost: Nat) (state: s) (rest: Set (Nat, s))
    (queued: Graph.Queued graph sources (Some ((cost, state), rest))): state ∈ graph.universe sources :=
  Exists.elim queued (queue facts =>
    And.right facts cost state (Set.containsMin queue (cost, state) (And.left (Set.popMinSome queue (cost, state) rest (And.left facts)))))

--| How many pairs the queue popped as `popped` held.
def Graph.poppedSize [auto ord: Ord s] (popped: Option ((Nat, s), Set (Nat, s))): Nat :=
  match popped with
    | None => 0
    | Some (least, rest) => rest.size + 1

--| Popping a queue tells of no more pairs than it holds.
theorem Graph.poppedSizeAtMost [auto ord: Ord s] (queue: Set (Nat, s)): Graph.poppedSize queue.popMin ≤ queue.size :=
  match found: queue.popMin with
    | None => rfl
    | Some (least, rest) => Set.sizePopMin queue least rest found

--| Dijkstra's algorithm, with its costs in tables of `costs`: `popped` is
--| the least (cost, state) pair still to look at with the rest of the
--| queue, or nothing when the queue is empty; `settled` the least cost
--| found for each state settled so far; `best` the least cost each state
--| has been queued at. The popped pair settles its state, unless it already
--| is, and queues the states its edges get to for less than `best` has. A
--| pair left behind by a cheaper one for its state is dropped when popped,
--| its state settled by then. The queue it was popped from is not an
--| argument, only `queued`, a proof about it: an argument would keep that
--| queue alive while `rest` is popped and pushed to, so none of its cells
--| could be updated in place.
@[tailrec]
def Graph.searchFrom [auto ord: Ord s] (graph: Graph s) (costs: Graph.Costs s t) (sources: List (s, Nat)) (settled: t) (best: t)
    (popped: Option ((Nat, s), Set (Nat, s))) (queued: Graph.Queued graph sources popped): t
    decreasing (Graph.unsettledAt costs (graph.universe sources) settled, Graph.poppedSize popped)
:=
  match popped with
    | None => settled
    | Some ((cost, state), rest) =>
      let restQueued := Graph.queuedRest graph sources (cost, state) rest queued
      if fresh: costs.has settled state = False then
        let relaxed := Graph.relaxEdges costs cost (graph.edges state) rest best
        Graph.searchFrom graph costs sources (costs.set settled state cost) relaxed.snd relaxed.fst.popMin
          (Graph.queuedPop graph sources relaxed.fst (Graph.relaxedQueued graph costs sources state cost rest best restQueued))
          [decreasing :=
            Nat.LexLess.First
              (Graph.unsettledAtFewer costs (graph.universe sources) settled (costs.set settled state cost)
                (other there => costs.hasSetKeeps settled state cost there) state
                (Graph.queuedLeast graph sources cost state rest queued) fresh (costs.hasSetSame settled state cost))]
      else
        Graph.searchFrom graph costs sources settled best rest.popMin (Graph.queuedPop graph sources rest restQueued)
          [decreasing := Nat.LexLess.Second rfl (omega [Graph.poppedSizeAtMost rest])]

--| Dijkstra's search with its costs in tables of `costs`: the table of
--| least costs it settles, from the sources, each given with the cost of
--| starting there. `Graph.distances` is this at [`Graph.mapCosts`].
def Graph.distancesWith [auto ord: Ord s] (graph: Graph s) (costs: Graph.Costs s t) (sources: List (s, Nat)): t :=
  let start := Graph.relaxEdges costs 0 sources Set.empty costs.empty
  graph.searchFrom costs sources costs.empty start.snd start.fst.popMin
    (Graph.queuedPop graph sources start.fst (Graph.startQueued graph costs sources))

--| The least cost to each state reachable from one of the sources, each
--| given with the cost of starting there. With an `index` that numbers the
--| states densely, such as a grid's positions row by row, the search keeps
--| the numbered states' costs in arrays rather than maps, which is faster;
--| [`Graph.distancesCorrect`] and [`Graph.distancesShortest`] hold for any
--| index, so the costs are the same. Without one (an index of size 0) every
--| cost is kept in a map.
def Graph.distances [auto ord: Ord s] (graph: Graph s) (index: Graph.Index s := Graph.Index.none) (sources: List (s, Nat)): Map s Nat :=
  -- Kept small enough for the optimiser to inline at each call, so that
  -- the map branch's `Ord` is the caller's own instance and the tree's
  -- lookups are specialised to it, as they were before there was an index
  -- (6% of day 15's instructions otherwise). So the indexed branch is a
  -- call, of a definition too large to inline.
  match index.size with
    | Zero => graph.distancesWith Graph.mapCosts sources
    | Succ _ => graph.distancesByIndex index sources

--| `Graph.distances` with the costs of the states `index` numbers in arrays:
--| the search's table, as [`Graph.IndexTable.toMap`] reads it.
def Graph.distancesByIndex [auto ord: Ord s] (graph: Graph s) (index: Graph.Index s) (sources: List (s, Nat)): Map s Nat :=
  let table := graph.distancesWith (Graph.indexCosts index) sources
  Map.fromList (index.entries 0 table.cells.toList ++ table.rest.toList)

--| A cost the search still has to account for: the state is queued for no
--| more, or settled for no more.
def Graph.Pending [auto ord: Ord s] (costs: Graph.Costs s t) (queue: Set (Nat, s)) (settled: t) (cost: Nat) (state: s): Prop :=
  (Exists Nat (found => (found ≤ cost) ∧ (queue.contains (found, state) = True))) ∨ (Graph.BoundBy (costs.get settled) cost state)

--| A pending cost is pending for any larger one.
theorem Graph.pendingWeaken [auto ord: Ord s] (costs: Graph.Costs s t) (queue: Set (Nat, s)) (settled: t) (cost: Nat) (more: Nat) (state: s)
    (pending: Graph.Pending costs queue settled cost state) (le: cost ≤ more): Graph.Pending costs queue settled more state :=
  match pending with
    | Inl (Witness found (Both below there)) => Inl (Witness found (Both (omega [below, le]) there))
    | Inr bound => Inr (Graph.boundByWeaken (costs.get settled) cost more state bound le)

--| What holds at each step of the search.
--| Every queued pair and settled state is reached for its cost; each
--| source, each edge out of a settled state, and each cost in `best` is
--| pending; and nothing settled costs more than anything queued.
def Graph.SearchState [auto ord: Ord s] (graph: Graph s) (costs: Graph.Costs s t) (sources: List (s, Nat)) (reach: s → Nat → Prop) (queue: Set (Nat, s))
    (settled: t) (best: t): Prop :=
  (∀ (cost: Nat) (state: s) => queue.contains (cost, state) = True → reach state cost) ∧ ((∀ (state: s) (cost: Nat) => costs.get settled state = Some cost → reach state cost) ∧ ((∀ (source: s) (start: Nat) => (source, start) ∈ sources → Graph.Pending costs queue settled start source) ∧ ((∀ (state: s) (cost: Nat) => costs.get settled state = Some cost → ∀ (next: s) (weight: Nat) => (next, weight) ∈ graph.edges state →
    Graph.Pending costs queue settled (cost + weight) next) ∧ ((∀ (state: s) (cost: Nat) => costs.get settled state = Some cost → ∀ (other: Nat) (otherState: s) =>
    queue.contains (other, otherState) = True → cost ≤ other) ∧ (∀ (state: s) (cost: Nat) => costs.get best state = Some cost → Graph.Pending costs queue settled cost state)))))

--| A pending cost stays pending when the queue keeps all but the popped
--| pair, the settled states stay, and the popped state is settled for no
--| more than the popped cost.
theorem Graph.pendingKept [auto ord: Ord s] (costs: Graph.Costs s t) (queue: Set (Nat, s)) (newQueue: Set (Nat, s)) (settled: t) (newSettled: t)
    (poppedCost: Nat) (poppedState: s) (poppedFound: Nat)
    (kept: ∀ (entry: (Nat, s)) => queue.contains entry = True → entry ≠ (poppedCost, poppedState) → newQueue.contains entry = True)
    (stays: ∀ (state: s) (found: Nat) => costs.get settled state = Some found → costs.get newSettled state = Some found)
    (popped: costs.get newSettled poppedState = Some poppedFound) (cheaper: poppedFound ≤ poppedCost) (cost: Nat) (state: s)
    (pending: Graph.Pending costs queue settled cost state): Graph.Pending costs newQueue newSettled cost state :=
  match pending with
    | Inr (Witness found (Both got le)) => Inr (Witness found (Both (stays state found got) le))
    | Inl (Witness found (Both below there)) =>
      match same: (found, state) == (poppedCost, poppedState) with
        | True =>
          let equal := DecEq.sound [x := (found, state)] [y := (poppedCost, poppedState)] same
          let costsEqual: found = poppedCost := Eq.cong Pair.fst equal
          Inr (Witness poppedFound (Both (rewrite Eq.cong Pair.snd equal in popped) (omega [costsEqual, cheaper, below])))
        | False => Inl (Witness found (Both below (kept (found, state) there (DecEq.soundFalse _ _ same))))

--| With nothing queued, a pending cost is a bound.
theorem Graph.boundOfPending [auto ord: Ord s] (costs: Graph.Costs s t) (queue: Set (Nat, s)) (settled: t) (empty: queue.popMin = None) (cost: Nat)
    (state: s) (pending: Graph.Pending costs queue settled cost state): Graph.BoundBy (costs.get settled) cost state :=
  match pending with
    | Inr bound => bound
    | Inl (Witness found (Both below there)) =>
      Void.exfalso (Bool.falseNotTrue (Eq.trans (Eq.sym (Set.missingOfMinNone queue (Set.popMinNone queue empty) (found, state))) there))

--| Dropping a popped pair whose state is settled keeps the search state.
theorem Graph.skipKeeps [auto ord: Ord s] (graph: Graph s) (costs: Graph.Costs s t) (sources: List (s, Nat)) (reach: s → Nat → Prop)
    (queue: Set (Nat, s)) (settled: t) (best: t) (cost: Nat) (state: s) (found: queue.min = Some (cost, state))
    (taken: costs.has settled state = True) (invariant: Graph.SearchState graph costs sources reach queue settled best):
    Graph.SearchState graph costs sources reach (queue.remove (cost, state)) settled best :=
  let (Both queuedReach (Both settledReached (Both sourcesPending (Both edgesPending (Both ordered bestPending))))) := invariant
  let inQueue := Set.containsMin queue (cost, state) found
  Exists.elim (costs.getOfHas taken) (settledCost got =>
    let cheaper := ordered state settledCost got cost state inQueue
    let keep := Graph.pendingKept costs queue (queue.remove (cost, state)) settled settled cost state settledCost
      (entry there apart => Eq.trans (Set.containsRemoveOther queue (cost, state) entry apart) there) (other value got => got) got cheaper
    Both (other otherState there => queuedReach other otherState (Set.containsOfRemove queue (cost, state) (other, otherState) there))
      (Both settledReached
        (Both (source start member => keep start source (sourcesPending source start member))
          (Both
            (from fromCost got next weight edge => keep (fromCost + weight) next (edgesPending from fromCost got next weight edge))
            (Both
              (from fromCost got other otherState there =>
                ordered from fromCost got other otherState (Set.containsOfRemove queue (cost, state) (other, otherState) there))
              (other otherCost got => keep otherCost other (bestPending other otherCost got)))))))

--| Settling the popped state and relaxing its edges keeps the search
--| state.
theorem Graph.settleKeeps [auto ord: Ord s] (graph: Graph s) (costs: Graph.Costs s t) (sources: List (s, Nat)) (reach: s → Nat → Prop)
    (edgesReach: ∀ (state: s) (cost: Nat) => reach state cost → ∀ (next: s) (weight: Nat) => (next, weight) ∈ graph.edges state →
      reach next (cost + weight))
    (queue: Set (Nat, s)) (settled: t) (best: t) (cost: Nat) (state: s) (found: queue.min = Some (cost, state))
    (fresh: costs.has settled state = False) (invariant: Graph.SearchState graph costs sources reach queue settled best):
    Graph.SearchState graph costs sources reach (Graph.relaxEdges costs cost (graph.edges state) (queue.remove (cost, state)) best).fst
      (costs.set settled state cost) (Graph.relaxEdges costs cost (graph.edges state) (queue.remove (cost, state)) best).snd :=
  let (Both queuedReach (Both settledReached (Both sourcesPending (Both edgesPending (Both ordered bestPending))))) := invariant
  let rest := queue.remove (cost, state)
  let relaxed := Graph.relaxEdges costs cost (graph.edges state) rest best
  let inQueue := Set.containsMin queue (cost, state) found
  let reached := queuedReach cost state inQueue
  let poppedGot: costs.get (costs.set settled state cost) state = Some cost := costs.getSet settled state cost
  let keep := Graph.pendingKept costs queue relaxed.fst settled (costs.set settled state cost) cost state cost
    (entry there apart =>
      Graph.relaxKeeps costs cost (graph.edges state) rest best entry (Eq.trans (Set.containsRemoveOther queue (cost, state) entry apart) there))
    (other value got => costs.getSetKeeps settled state cost fresh got) poppedGot (Nat.leRefl cost)
  let atLeast: ∀ (other: Nat) (otherState: s) => relaxed.fst.contains (other, otherState) = True → cost ≤ other :=
    other otherState there =>
      match Graph.relaxAdded costs cost (graph.edges state) rest best other otherState there with
        | Inl inRest => Graph.minLeast queue cost state found other otherState (Set.containsOfRemove queue (cost, state) (other, otherState) inRest)
        | Inr (Witness weight (Both edge costsEqual)) => rewrite costsEqual in omega
  let newBest: ∀ (other: s) (otherCost: Nat) => costs.get relaxed.snd other = Some otherCost →
      Graph.Pending costs relaxed.fst (costs.set settled state cost) otherCost other :=
    other otherCost got =>
      match Graph.relaxBest costs cost (graph.edges state) rest best other otherCost got with
        | Inl old => keep otherCost other (bestPending other otherCost old)
        | Inr queued => Inl (Witness otherCost (Both (Nat.leRefl otherCost) queued))
  Both
    (other otherState there =>
      match Graph.relaxAdded costs cost (graph.edges state) rest best other otherState there with
        | Inl inRest => queuedReach other otherState (Set.containsOfRemove queue (cost, state) (other, otherState) inRest)
        | Inr (Witness weight (Both edge costsEqual)) => rewrite costsEqual in edgesReach state cost reached otherState weight edge)
    (Both
      (other otherCost got =>
        match costs.getSetCases got with
          | Inl (Both same costsEqual) => rewrite same, costsEqual in reached
          | Inr old => settledReached other otherCost old)
      (Both (source start member => keep start source (sourcesPending source start member))
        (Both
          (from fromCost got next weight edge =>
            match costs.getSetCases got with
              | Inl (Both same costsEqual) =>
                let (Witness bestCost (Both bestGot le)) :=
                  Graph.relaxCovers costs cost (graph.edges state) rest best next weight (rewrite <- same in edge)
                rewrite costsEqual in
                  Graph.pendingWeaken costs relaxed.fst (costs.set settled state cost) bestCost (cost + weight) next (newBest next bestCost bestGot) le
              | Inr old => keep (fromCost + weight) next (edgesPending from fromCost old next weight edge))
          (Both
            (from fromCost got other otherState there =>
              match costs.getSetCases got with
                | Inl (Both same costsEqual) => rewrite costsEqual in atLeast other otherState there
                | Inr old => omega [ordered from fromCost old cost state inQueue, atLeast other otherState there])
            newBest))))

--| The search returns what `SearchResultBy` says, from any search state.
theorem Graph.searchFromCorrect [auto ord: Ord s] (graph: Graph s) (costs: Graph.Costs s t) (sources: List (s, Nat)) (reach: s → Nat → Prop)
    (edgesReach: ∀ (state: s) (cost: Nat) => reach state cost → ∀ (next: s) (weight: Nat) => (next, weight) ∈ graph.edges state →
      reach next (cost + weight))
    (queue: Set (Nat, s)) (settled: t) (best: t)
    (popped: Option ((Nat, s), Set (Nat, s))) (queued: Graph.Queued graph sources popped) (found: queue.popMin = popped)
    (invariant: Graph.SearchState graph costs sources reach queue settled best):
    Graph.SearchResultBy graph sources reach (costs.get (graph.searchFrom costs sources settled best popped queued))
    decreasing (Graph.unsettledAt costs (graph.universe sources) settled, queue.size)
:=
  match popped with
    | None =>
      rewrite Graph.searchFrom.eq1 graph costs sources settled best queued in
        let (Both queuedReach (Both settledReached (Both sourcesPending (Both edgesPending others)))) := invariant
        Both settledReached
          (Both (source start member => Graph.boundOfPending costs queue settled found start source (sourcesPending source start member))
            (from fromCost got next weight edge =>
              Graph.boundOfPending costs queue settled found (fromCost + weight) next (edgesPending from fromCost got next weight edge)))
    | Some ((cost, state), rest) =>
      let (Both least restIs) := Set.popMinSome queue (cost, state) rest found
      let restQueued := Graph.queuedRest graph sources (cost, state) rest queued
      match taken: costs.has settled state with
        | True =>
          rewrite Graph.searchFrom.eq2.ifFalse graph costs sources settled best cost state rest queued taken in
            Graph.searchFromCorrect graph costs sources reach edgesReach rest settled best rest.popMin (Graph.queuedPop graph sources rest restQueued) rfl
              (rewrite restIs in Graph.skipKeeps graph costs sources reach queue settled best cost state least taken invariant)
              [decreasing := Nat.LexLess.Second rfl (Set.sizePopMin queue (cost, state) rest found)]
        | False =>
          let relaxed := Graph.relaxEdges costs cost (graph.edges state) rest best
          rewrite Graph.searchFrom.eq2.ifTrue graph costs sources settled best cost state rest queued taken in
            Graph.searchFromCorrect graph costs sources reach edgesReach relaxed.fst (costs.set settled state cost) relaxed.snd relaxed.fst.popMin
              (Graph.queuedPop graph sources relaxed.fst (Graph.relaxedQueued graph costs sources state cost rest best restQueued)) rfl
              (rewrite restIs in Graph.settleKeeps graph costs sources reach edgesReach queue settled best cost state least taken invariant)
              [decreasing :=
                Nat.LexLess.First
                  (Graph.unsettledAtFewer costs (graph.universe sources) settled (costs.set settled state cost)
                    (other there => costs.hasSetKeeps settled state cost there) state
                    (Graph.queuedLeast graph sources cost state rest queued) taken (costs.hasSetSame settled state cost))]

--| Dijkstra's search over any cost table returns what `SearchResultBy`
--| says of the table it ends with, for any `reach` that holds at each
--| source for its starting cost and along each edge.
theorem Graph.distancesWithCorrect [auto ord: Ord s] (graph: Graph s) (costs: Graph.Costs s t) (sources: List (s, Nat)) (reach: s → Nat → Prop)
    (sourcesReach: ∀ (source: s) (start: Nat) => (source, start) ∈ sources → reach source start)
    (edgesReach: ∀ (state: s) (cost: Nat) => reach state cost → ∀ (next: s) (weight: Nat) => (next, weight) ∈ graph.edges state →
      reach next (cost + weight)):
    Graph.SearchResultBy graph sources reach (costs.get (graph.distancesWith costs sources)) :=
  let start := Graph.relaxEdges costs 0 sources Set.empty costs.empty
  let nothing: ∀ (state: s) (cost: Nat) => costs.get costs.empty state = Some cost → Void :=
    state cost got => Option.noneNotSome cost (Eq.trans (Eq.sym (costs.getEmpty state)) got)
  let startBest: ∀ (state: s) (cost: Nat) => costs.get start.snd state = Some cost → Graph.Pending costs start.fst costs.empty cost state :=
    state cost got =>
      match Graph.relaxBest costs 0 sources Set.empty costs.empty state cost got with
        | Inl none => Void.exfalso (nothing state cost none)
        | Inr queued => Inl (Witness cost (Both (Nat.leRefl cost) queued))
  let initial: Graph.SearchState graph costs sources reach start.fst costs.empty start.snd :=
    Both
      (cost state there =>
        match Graph.relaxAdded costs 0 sources Set.empty costs.empty cost state there with
          | Inl none => cases
          | Inr (Witness begin (Both member costsEqual)) =>
            let same: cost = begin := omega
            rewrite same in sourcesReach state begin member)
      (Both (state cost got => Void.exfalso (nothing state cost got))
        (Both
          (source begin member =>
            let (Witness found (Both got le)) := Graph.relaxCovers costs 0 sources Set.empty costs.empty source begin member
            Graph.pendingWeaken costs start.fst costs.empty found begin source (startBest source found got) (omega [le]))
          (Both (state cost got => Void.exfalso (nothing state cost got))
            (Both (state cost got => Void.exfalso (nothing state cost got)) startBest))))
  Graph.searchFromCorrect graph costs sources reach edgesReach start.fst costs.empty start.snd start.fst.popMin
    (Graph.queuedPop graph sources start.fst (Graph.startQueued graph costs sources)) rfl initial

--| `SearchResultBy` for one lookup holds for any lookup that agrees with
--| it.
theorem Graph.searchResultBySame (graph: Graph s) (sources: List (s, Nat)) (reach: s → Nat → Prop) (get: s → Option Nat) (other: s → Option Nat)
    (same: ∀ (state: s) => other state = get state) (result: Graph.SearchResultBy graph sources reach get): Graph.SearchResultBy graph sources reach other :=
  let (Both reached (Both sourcesBound closed)) := result
  let bound: ∀ (cost: Nat) (state: s) => Graph.BoundBy get cost state → Graph.BoundBy other cost state :=
    cost state (Witness found (Both got le)) => Witness found (Both (Eq.trans (same state) got) le)
  Both (state cost got => reached state cost (Eq.trans (Eq.sym (same state)) got))
    (Both (source start member => bound start source (sourcesBound source start member))
      (state cost got next weight edge => bound (cost + weight) next (closed state cost (Eq.trans (Eq.sym (same state)) got) next weight edge)))

--| Dijkstra's search returns what `SearchResult` says, for any `reach` that
--| holds at each source for its starting cost and along each edge, with
--| any `index`.
theorem Graph.distancesCorrect [auto ord: Ord s] (graph: Graph s) (index: Graph.Index s := Graph.Index.none) (sources: List (s, Nat)) (reach: s → Nat → Prop)
    (sourcesReach: ∀ (source: s) (start: Nat) => (source, start) ∈ sources → reach source start)
    (edgesReach: ∀ (state: s) (cost: Nat) => reach state cost → ∀ (next: s) (weight: Nat) => (next, weight) ∈ graph.edges state →
      reach next (cost + weight)):
    Graph.SearchResult graph sources reach (graph.distances (index := index) sources) :=
  match empty: index.size with
    | Zero => Graph.distancesWithCorrect graph Graph.mapCosts sources reach sourcesReach edgesReach
    | Succ _ =>
      let table := graph.distancesWith (Graph.indexCosts index) sources
      Graph.searchResultBySame graph sources reach ((Graph.indexCosts index).get table) (state => (Graph.IndexTable.toMap index table).get state)
        (state => Graph.IndexTable.getToMap index table state)
        (Graph.distancesWithCorrect graph (Graph.indexCosts index) sources reach sourcesReach edgesReach)

--| Each cost Dijkstra's search finds is a walk's from a source, and no walk
--| from a source costs less, with any `index`.
theorem Graph.distancesShortest [auto ord: Ord s] (graph: Graph s) (index: Graph.Index s := Graph.Index.none) (sources: List (s, Nat)):
    Graph.Shortest graph sources (graph.distances (index := index) sources) :=
  Graph.shortestOfResult graph sources (graph.distances (index := index) sources)
    (Graph.distancesCorrect graph (index := index) sources (graph.Reached sources) (Graph.reachedSources graph sources) (Graph.reachedEdges graph sources))

-- Breadth-first search

--| Each edge's state not settled yet: settled at `depth`, and put on
--| `next`.
@[tailrec]
def Graph.visitEdges [auto ord: Ord s] (depth: Nat): (edges: List (s, Nat)) → (settled: Map s Nat) → (next: List s) → (Map s Nat, List s)
  | [], settled, next => (settled, next)
  | [(state, weight), ..rest], settled, next =>
    if settled.contains state then Graph.visitEdges depth rest settled next
    else Graph.visitEdges depth rest (settled.insert state depth) [state, ..next]

--| What visiting edges settled stays settled.
theorem Graph.visitGrows [auto ord: Ord s] (depth: Nat) (edges: List (s, Nat)) (settled: Map s Nat) (next: List s) (state: s) (cost: Nat) (got: settled.get state = Some cost): (Graph.visitEdges depth edges settled next).fst.get state = Some cost :=
  match edges with
    | [] => got
    | [(target, weight), ..rest] =>
      match there: settled.contains target with
        | True => Graph.visitGrows depth rest settled next state cost got
        | False =>
          Graph.visitGrows depth rest (settled.insert target depth) [target, ..next] state cost
            (Map.getInsertKeeps settled target depth there state cost got)

--| Visiting edges keeps what was on the list on it.
theorem Graph.visitListed [auto ord: Ord s] (depth: Nat) (edges: List (s, Nat)) (settled: Map s Nat) (next: List s) (state: s)
    (member: state ∈ next): state ∈ (Graph.visitEdges depth edges settled next).snd :=
  match edges with
    | [] => member
    | [(target, weight), ..rest] =>
      match there: settled.contains target with
        | True => Graph.visitListed depth rest settled next state member
        | False => Graph.visitListed depth rest (settled.insert target depth) [target, ..next] state (Inr member)

--| What visiting edges settles anew is at `depth`, and put on the list.
theorem Graph.visitNew [auto ord: Ord s] (depth: Nat) (edges: List (s, Nat)) (settled: Map s Nat) (next: List s) (state: s) (cost: Nat) (got: (Graph.visitEdges depth edges settled next).fst.get state = Some cost):
    (settled.get state = Some cost) ∨ ((cost = depth) ∧ ((state ∈ (Graph.visitEdges depth edges settled next).snd) ∧ (Exists Nat (weight => (state, weight) ∈ edges)))) :=
  match edges with
    | [] => Inl got
    | [(target, weight), ..rest] =>
      match there: settled.contains target with
        | True =>
          match Graph.visitNew depth rest settled next state cost got with
            | Inl old => Inl old
            | Inr (Both costs (Both listed (Witness found edge))) => Inr (Both costs (Both listed (Witness found (Inr edge))))
        | False =>
          match Graph.visitNew depth rest (settled.insert target depth) [target, ..next] state cost got with
            | Inr (Both costs (Both listed (Witness found edge))) => Inr (Both costs (Both listed (Witness found (Inr edge))))
            | Inl inserted =>
              match Map.getInsertCases settled target depth state cost inserted with
                | Inr old => Inl old
                | Inl (Both same costs) =>
                  Inr
                    (Both costs
                      (Both (Graph.visitListed depth rest (settled.insert target depth) [target, ..next] state (Inl (Eq.sym same)))
                        (Witness weight (Inl (rewrite same in rfl)))))

--| What is on the list after visiting edges was on it, or wasn't settled
--| before and is now, at `depth`, an edge's state.
theorem Graph.visitAdded [auto ord: Ord s] (depth: Nat) (edges: List (s, Nat)) (settled: Map s Nat) (next: List s) (state: s)
    (member: state ∈ (Graph.visitEdges depth edges settled next).snd):
    (state ∈ next) ∨ ((settled.contains state = False) ∧ (((Graph.visitEdges depth edges settled next).fst.get state = Some depth) ∧ (Exists Nat (weight => (state, weight) ∈ edges)))) :=
  match edges with
    | [] => Inl member
    | [(target, weight), ..rest] =>
      match there: settled.contains target with
        | True =>
          match Graph.visitAdded depth rest settled next state member with
            | Inl old => Inl old
            | Inr (Both fresh (Both got (Witness found edge))) => Inr (Both fresh (Both got (Witness found (Inr edge))))
        | False =>
          match Graph.visitAdded depth rest (settled.insert target depth) [target, ..next] state member with
            | Inl (Inl same) =>
              rewrite <- same in
                Inr
                  (Both there
                    (Both
                      (Graph.visitGrows depth rest (settled.insert target depth) [target, ..next] target depth
                        (Map.getInsert target depth settled))
                      (Witness weight (Inl rfl))))
            | Inl (Inr old) => Inl old
            | Inr (Both fresh (Both got (Witness found edge))) =>
              let before: settled.contains state = False :=
                match was: settled.contains state with
                  | False => rfl
                  | True => Void.exfalso (Bool.falseNotTrue (Eq.trans (Eq.sym fresh) (Map.containsInsertKeeps settled target depth state was)))
              Inr (Both before (Both got (Witness found (Inr edge))))

--| After visiting edges, every edge's state is settled.
theorem Graph.visitCovers [auto ord: Ord s] (depth: Nat) (edges: List (s, Nat)) (settled: Map s Nat) (next: List s) (state: s) (weight: Nat) (member: (state, weight) ∈ edges): (Graph.visitEdges depth edges settled next).fst.contains state = True :=
  match edges with
    | [(target, targetWeight), ..rest] =>
      let settles: ∀ (more: Map s Nat) (added: List s) => more.contains state = True →
          (Graph.visitEdges depth rest more added).fst.contains state = True :=
        more added there =>
          Exists.elim (Map.getOfContains more state there) (cost got =>
            Map.containsOfGet _ state cost (Graph.visitGrows depth rest more added state cost got))
      match there: settled.contains target with
        | True =>
          match member with
            | Inl here => settles settled next (rewrite <- Eq.cong Pair.fst here in there)
            | Inr later => Graph.visitCovers depth rest settled next state weight later
        | False =>
          match member with
            | Inl here =>
              settles (settled.insert target depth) [target, ..next]
                (rewrite <- Eq.cong Pair.fst here in Map.containsInsertSame settled target depth)
            | Inr later => Graph.visitCovers depth rest (settled.insert target depth) [target, ..next] state weight later

--| One level of the search: the edges out of the frontier, visited.
def Graph.visitFrontier [auto ord: Ord s] (graph: Graph s) (depth: Nat) (frontier: List s) (settled: Map s Nat): (Map s Nat, List s) :=
  Graph.visitEdges depth (frontier.flatMap graph.edges) settled []

--| A frontier visited with states added leaves fewer unsettled.
theorem Graph.visitFewer [auto ord: Ord s] (graph: Graph s) (depth: Nat) (frontier: List s) (settled: Map s Nat) (more: Map s Nat)
    (first: s) (rest: List s) (found: graph.visitFrontier depth frontier settled = (more, [first, ..rest])):
    Graph.unsettledIn graph.states more < Graph.unsettledIn graph.states settled :=
  let edges := frontier.flatMap graph.edges
  let listedFirst: first ∈ (Graph.visitEdges depth edges settled []).snd := rewrite found in Inl rfl
  let moreIs: (Graph.visitEdges depth edges settled []).fst = more := Eq.cong Pair.fst found
  match Graph.visitAdded depth edges settled [] first listedFirst with
    | Inl none => Void.exfalso none
    | Inr (Both fresh (Both got (Witness weight edge))) =>
      List.anyElim (from => (first, weight) ∈ graph.edges from) (Graph.unsettledIn graph.states more < Graph.unsettledIn graph.states settled)
        frontier (List.memFlatMapElim graph.edges (first, weight) frontier edge) (from inFrontier fromEdge =>
          Graph.unsettledFewer graph.states settled more
            (state there =>
              Exists.elim (Map.getOfContains settled state there) (cost old =>
                Map.containsOfGet more state cost (rewrite <- moreIs in Graph.visitGrows depth edges settled [] state cost old)))
            first (graph.listed from first weight fromEdge) fresh (Map.containsOfGet more first depth (rewrite <- moreIs in got)))

--| Breadth-first search: `frontier` holds the states settled at `depth`.
--| The states their edges lead to that aren't settled yet are settled at
--| `depth + 1`, `visited` with the next frontier.
@[tailrec]
def Graph.breadthFrom [auto ord: Ord s] (graph: Graph s) (depth: Nat) (settled: Map s Nat) (frontier: List s):
    (visited: (Map s Nat, List s)) → (found: graph.visitFrontier (depth + 1) frontier settled = visited) → Map s Nat
    decreasing Graph.unsettledIn graph.states settled
  | (more, []), found => more
  | (more, [first, ..rest]), found =>
    graph.breadthFrom (depth + 1) more [first, ..rest] (graph.visitFrontier (depth + 1 + 1) [first, ..rest] more) rfl
      [decreasing := Graph.visitFewer graph (depth + 1) frontier settled more first rest found]

--| The fewest edges from any of the sources to each state reachable from
--| them, found level by level. The edges' costs are ignored, so these are
--| the least costs only for a graph whose edges each cost 1, which is what
--| [`Graph.breadthFirstCorrect`] and [`Graph.breadthFirstShortest`] assume;
--| otherwise use [`Graph.distances`].
def Graph.breadthFirst [auto ord: Ord s] (graph: Graph s) (sources: List s): Map s Nat :=
  let start := Graph.visitEdges 0 (sources.map (source => (source, 0))) Map.empty []
  graph.breadthFrom 0 start.fst start.snd (graph.visitFrontier (0 + 1) start.snd start.fst) rfl

theorem Graph.breadthDone [auto ord: Ord s] (graph: Graph s) (depth: Nat) (settled: Map s Nat) (frontier: List s) (more: Map s Nat)
    (found: graph.visitFrontier (depth + 1) frontier settled = (more, [])): graph.breadthFrom depth settled frontier (more, []) found = more :=
  rewrite Graph.breadthFrom.unfold graph depth settled frontier (more, []) found in rfl

theorem Graph.breadthStep [auto ord: Ord s] (graph: Graph s) (depth: Nat) (settled: Map s Nat) (frontier: List s) (more: Map s Nat) (first: s)
    (rest: List s) (found: graph.visitFrontier (depth + 1) frontier settled = (more, [first, ..rest])):
    graph.breadthFrom depth settled frontier (more, [first, ..rest]) found
      = graph.breadthFrom (depth + 1) more [first, ..rest] (graph.visitFrontier (depth + 1 + 1) [first, ..rest] more) rfl :=
  rewrite Graph.breadthFrom.unfold graph depth settled frontier (more, [first, ..rest]) found in rfl

--| What holds at each level of the search, for a `reach` that holds at the sources for 0 and along every edge for one more.
--| Every settled state is reached for its cost, at most `depth`; the frontier
--| is exactly the states settled at `depth`; each edge out of a state settled
--| below it leads to one settled for one more at most; and each source is
--| settled at 0.
def Graph.BreadthState [auto ord: Ord s] (graph: Graph s) (sources: List s) (reach: s → Nat → Prop) (depth: Nat) (settled: Map s Nat)
    (frontier: List s): Prop :=
  (∀ (state: s) (cost: Nat) => settled.get state = Some cost → (reach state cost) ∧ (cost ≤ depth)) ∧ ((∀ (state: s) => (state ∈ frontier) ↔ (settled.get state = Some depth)) ∧ ((∀ (state: s) (cost: Nat) => settled.get state = Some cost → cost < depth → ∀ (next: s) (weight: Nat) =>
    (next, weight) ∈ graph.edges state → Graph.Bound settled (cost + 1) next) ∧ (∀ (source: s) => source ∈ sources → Graph.Bound settled 0 source)))

--| A bound survives visiting.
theorem Graph.visitBound [auto ord: Ord s] (depth: Nat) (edges: List (s, Nat)) (settled: Map s Nat) (next: List s) (cost: Nat) (state: s)
    (bound: Graph.Bound settled cost state): Graph.Bound (Graph.visitEdges depth edges settled next).fst cost state :=
  Exists.elim bound (found both => Witness found (Both (Graph.visitGrows depth edges settled next state found (And.left both)) (And.right both)))

--| What breadth-first search returns, whatever its edges cost: `SearchResult`
--| with each edge adding one, since the search counts edges. A `reach` that
--| holds at the sources and one more along each edge is all it needs.
def Graph.StepResult [auto ord: Ord s] (graph: Graph s) (sources: List (s, Nat)) (reach: s → Nat → Prop) (result: Map s Nat): Prop :=
  (∀ (state: s) (cost: Nat) => result.get state = Some cost → reach state cost) ∧ ((∀ (source: s) (start: Nat) => (source, start) ∈ sources → Graph.Bound result start source) ∧ (∀ (state: s) (cost: Nat) => result.get state = Some cost → ∀ (next: s) (weight: Nat) => (next, weight) ∈ graph.edges state →
    Graph.Bound result (cost + 1) next))

--| Each edge out of the frontier leads to a state settled for one more at
--| most, after visiting it.
theorem Graph.frontierClosed [auto ord: Ord s] (graph: Graph s) (sources: List s) (reach: s → Nat → Prop) (depth: Nat) (settled: Map s Nat)
    (frontier: List s) (invariant: Graph.BreadthState graph sources reach depth settled frontier) (state: s) (inFrontier: state ∈ frontier)
    (next: s) (weight: Nat) (edge: (next, weight) ∈ graph.edges state):
    Graph.Bound (graph.visitFrontier (depth + 1) frontier settled).fst (depth + 1) next :=
  let (Both settledReach rest) := invariant
  let edges := frontier.flatMap graph.edges
  let covered := Graph.visitCovers (depth + 1) edges settled [] next weight (List.memFlatMapIntro graph.edges state (next, weight) frontier inFrontier edge)
  Exists.elim (Map.getOfContains _ next covered) (cost got =>
    match Graph.visitNew (depth + 1) edges settled [] next cost got with
      | Inl old => Witness cost (Both got (omega [And.right (settledReach next cost old)]))
      | Inr (Both costs others) => Witness cost (Both got (omega [costs])))

--| With no next frontier, the search state is the search result.
theorem Graph.breadthDoneCorrect [auto ord: Ord s] (graph: Graph s) (sources: List s) (reach: s → Nat → Prop) (depth: Nat) (settled: Map s Nat)
    (frontier: List s) (more: Map s Nat) (found: graph.visitFrontier (depth + 1) frontier settled = (more, []))
    (invariant: Graph.BreadthState graph sources reach depth settled frontier):
    Graph.StepResult graph (sources.map (source => (source, 0))) reach more :=
  let (Both settledReach (Both atFrontier (Both closedBelow sourcesBound))) := invariant
  let edges := frontier.flatMap graph.edges
  let moreIs: (Graph.visitEdges (depth + 1) edges settled []).fst = more := Eq.cong Pair.fst found
  let nextIs: (Graph.visitEdges (depth + 1) edges settled []).snd = [] := Eq.cong Pair.snd found
  let old: ∀ (state: s) (cost: Nat) => more.get state = Some cost → settled.get state = Some cost :=
    state cost got =>
      match Graph.visitNew (depth + 1) edges settled [] state cost (rewrite moreIs in got) with
        | Inl was => was
        | Inr (Both costs (Both listed others)) => Void.exfalso (rewrite nextIs at listed in listed)
  let grows: ∀ (cost: Nat) (state: s) => Graph.Bound settled cost state → Graph.Bound more cost state :=
    cost state bound => rewrite <- moreIs in Graph.visitBound (depth + 1) edges settled [] cost state bound
  Both (state cost got => And.left (settledReach state cost (old state cost got)))
    (Both
      (source start member =>
        List.anyElim (other => (other, 0) = (source, start)) (Graph.Bound more start source) sources
          (List.memMapAny sources (source => (source, 0)) (source, start) member) (other inSources same =>
            rewrite <- Eq.cong Pair.snd same, <- Eq.cong Pair.fst same in grows 0 other (sourcesBound other inSources)))
      (state cost got next weight edge =>
        let was := old state cost got
        if below: cost < depth then grows (cost + 1) next (closedBelow state cost was below next weight edge)
        else
          let atDepth: cost = depth := omega [And.right (settledReach state cost was), below]
          let inFrontier := (atFrontier state).backward (rewrite <- atDepth in was)
          rewrite atDepth, <- moreIs in Graph.frontierClosed graph sources reach depth settled frontier invariant state inFrontier next weight edge))

--| One level keeps the search state.
theorem Graph.breadthKeeps [auto ord: Ord s] (graph: Graph s) (sources: List s) (reach: s → Nat → Prop)
    (edgesReach: ∀ (state: s) (cost: Nat) => reach state cost → ∀ (next: s) (weight: Nat) => (next, weight) ∈ graph.edges state →
      reach next (cost + 1)) (depth: Nat) (settled: Map s Nat)
    (frontier: List s) (more: Map s Nat) (nextFrontier: List s) (found: graph.visitFrontier (depth + 1) frontier settled = (more, nextFrontier))
    (invariant: Graph.BreadthState graph sources reach depth settled frontier): Graph.BreadthState graph sources reach (depth + 1) more nextFrontier :=
  let (Both settledReach (Both atFrontier (Both closedBelow sourcesBound))) := invariant
  let edges := frontier.flatMap graph.edges
  let moreIs: (Graph.visitEdges (depth + 1) edges settled []).fst = more := Eq.cong Pair.fst found
  let nextIs: (Graph.visitEdges (depth + 1) edges settled []).snd = nextFrontier := Eq.cong Pair.snd found
  let grows: ∀ (cost: Nat) (state: s) => Graph.Bound settled cost state → Graph.Bound more cost state :=
    cost state bound => rewrite <- moreIs in Graph.visitBound (depth + 1) edges settled [] cost state bound
  -- What is settled now was settled before, or is new at `depth + 1` and
  -- on the next frontier.
  let origin: ∀ (state: s) (cost: Nat) => more.get state = Some cost →
      (settled.get state = Some cost) ∨ ((cost = depth + 1) ∧ ((state ∈ nextFrontier) ∧ (Exists Nat (weight => (state, weight) ∈ edges)))) :=
    state cost got => rewrite <- nextIs in Graph.visitNew (depth + 1) edges settled [] state cost (rewrite moreIs in got)
  Both
    (state cost got =>
      match origin state cost got with
        | Inl old =>
          let (Both reached below) := settledReach state cost old
          Both reached (omega [below])
        | Inr (Both costs (Both listed (Witness weight edge))) =>
          List.anyElim (from => (state, weight) ∈ graph.edges from) ((reach state cost) ∧ (cost ≤ depth + 1)) frontier
            (List.memFlatMapElim graph.edges (state, weight) frontier edge) (from inFrontier fromEdge =>
              let fromGot := (atFrontier from).forward inFrontier
              let reached := edgesReach from depth (And.left (settledReach from depth fromGot)) state weight fromEdge
              rewrite costs in Both reached (Nat.leRefl (depth + 1))))
    (Both
      (state => {
        forward = listed =>
          match Graph.visitAdded (depth + 1) edges settled [] state (rewrite nextIs in listed) with
            | Inl none => Void.exfalso none
            | Inr (Both fresh (Both got others)) => rewrite <- moreIs in got,
        backward = got =>
          match origin state (depth + 1) got with
            | Inl old => Void.exfalso (omega [And.right (settledReach state (depth + 1) old)])
            | Inr (Both costs (Both listed others)) => listed
      })
      (Both
        (state cost got below next weight edge =>
          match origin state cost got with
            | Inr (Both costs others) => Void.exfalso (omega [costs, below])
            | Inl old =>
              if lower: cost < depth then grows (cost + 1) next (closedBelow state cost old lower next weight edge)
              else
                let atDepth: cost = depth := omega [below, lower]
                let inFrontier := (atFrontier state).backward (rewrite <- atDepth in old)
                rewrite atDepth, <- moreIs in Graph.frontierClosed graph sources reach depth settled frontier invariant state inFrontier next weight edge)
        (source member => grows 0 source (sourcesBound source member))))

--| The search returns what `SearchResult` says, from any search state.
theorem Graph.breadthFromCorrect [auto ord: Ord s] (graph: Graph s) (sources: List s) (reach: s → Nat → Prop)
    (edgesReach: ∀ (state: s) (cost: Nat) => reach state cost → ∀ (next: s) (weight: Nat) => (next, weight) ∈ graph.edges state →
      reach next (cost + 1)) (depth: Nat) (settled: Map s Nat)
    (frontier: List s)
    (visited: (Map s Nat, List s)) (found: graph.visitFrontier (depth + 1) frontier settled = visited)
    (invariant: Graph.BreadthState graph sources reach depth settled frontier):
    Graph.StepResult graph (sources.map (source => (source, 0))) reach (graph.breadthFrom depth settled frontier visited found)
    decreasing Graph.unsettledIn graph.states settled
:=
  match visited with
    | (more, []) =>
      rewrite Graph.breadthDone graph depth settled frontier more found in
        Graph.breadthDoneCorrect graph sources reach depth settled frontier more found invariant
    | (more, [first, ..rest]) =>
      rewrite Graph.breadthStep graph depth settled frontier more first rest found in
        Graph.breadthFromCorrect graph sources reach edgesReach (depth + 1) more [first, ..rest]
          (graph.visitFrontier (depth + 1 + 1) [first, ..rest] more) rfl
          (Graph.breadthKeeps graph sources reach edgesReach depth settled frontier more [first, ..rest] found invariant)
          [decreasing := Graph.visitFewer graph (depth + 1) frontier settled more first rest found]

--| Breadth-first search returns what `StepResult` says, whatever its edges
--| cost, for any `reach` that holds at each source for 0 and one more along
--| each edge.
theorem Graph.breadthFirstSteps [auto ord: Ord s] (graph: Graph s) (sources: List s) (reach: s → Nat → Prop)
    (sourcesReach: ∀ (source: s) => source ∈ sources → reach source 0)
    (edgesReach: ∀ (state: s) (cost: Nat) => reach state cost → ∀ (next: s) (weight: Nat) => (next, weight) ∈ graph.edges state →
      reach next (cost + 1)):
    Graph.StepResult graph (sources.map (source => (source, 0))) reach (graph.breadthFirst sources) :=
  let edges := sources.map (source => (source, 0))
  let start := Graph.visitEdges 0 edges Map.empty []
  let fromSource: ∀ (state: s) (weight: Nat) => (state, weight) ∈ edges → state ∈ sources :=
    state weight member =>
      List.anyElim (source => (source, 0) = (state, weight)) (state ∈ sources) sources (List.memMapAny sources (source => (source, 0)) (state, weight) member)
        (source inSources same => rewrite <- Eq.cong Pair.fst same in inSources)
  let origin: ∀ (state: s) (cost: Nat) => start.fst.get state = Some cost →
      (cost = 0) ∧ ((state ∈ start.snd) ∧ (state ∈ sources)) :=
    state cost got =>
      match Graph.visitNew 0 edges Map.empty [] state cost got with
        | Inl none => Void.exfalso (Option.noneNotSome cost none)
        | Inr (Both costs (Both listed (Witness weight edge))) => Both costs (Both listed (fromSource state weight edge))
  let initial: Graph.BreadthState graph sources reach 0 start.fst start.snd :=
    Both
      (state cost got =>
        let (Both costs (Both listed inSources)) := origin state cost got
        rewrite costs in Both (sourcesReach state inSources) (Nat.leRefl 0))
      (Both
        (state => {
          forward = listed =>
            match Graph.visitAdded 0 edges Map.empty [] state listed with
              | Inl none => Void.exfalso none
              | Inr (Both fresh (Both got others)) => got,
          backward = got => And.left (And.right (origin state 0 got))
        })
        (Both (state cost got below => Void.exfalso (omega [below]))
          (source member =>
            let covered := Graph.visitCovers 0 edges Map.empty [] source 0 (List.memMap sources source member (other => (other, 0)))
            Exists.elim (Map.getOfContains _ source covered) (cost got =>
              Witness cost (Both got (omega [And.left (origin source cost got)]))))))
  Graph.breadthFromCorrect graph sources reach edgesReach 0 start.fst start.snd (graph.visitFrontier (0 + 1) start.snd start.fst) rfl initial

--| Breadth-first search returns what `SearchResult` says, for a graph whose
--| edges each cost 1 and any `reach` that holds at each source for 0 and
--| along each edge.
theorem Graph.breadthFirstCorrect [auto ord: Ord s] (graph: Graph s) (sources: List s) (reach: s → Nat → Prop)
    (sourcesReach: ∀ (source: s) => source ∈ sources → reach source 0)
    (edgesReach: ∀ (state: s) (cost: Nat) => reach state cost → ∀ (next: s) (weight: Nat) => (next, weight) ∈ graph.edges state →
      reach next (cost + weight))
    (unit: ∀ (state next: s) (weight: Nat) => (next, weight) ∈ graph.edges state → weight = 1):
    Graph.SearchResult graph (sources.map (source => (source, 0))) reach (graph.breadthFirst sources) :=
  let (Both settledReach (Both sourcesBound closed)) :=
    Graph.breadthFirstSteps graph sources reach sourcesReach (state cost reached next weight edge =>
      rewrite unit state next weight edge at edgesReach state cost reached next weight edge)
  Both settledReach (Both sourcesBound (state cost got next weight edge =>
    rewrite unit state next weight edge in closed state cost got next weight edge))

--| On a graph whose edges each cost 1, each count breadth-first search finds
--| is a walk's from a source, and no walk from a source has fewer edges.
theorem Graph.breadthFirstShortest [auto ord: Ord s] (graph: Graph s) (sources: List s)
    (unit: ∀ (state next: s) (weight: Nat) => (next, weight) ∈ graph.edges state → weight = 1):
    Graph.Shortest graph (sources.map (source => (source, 0))) (graph.breadthFirst sources) :=
  let starts := sources.map (source => (source, 0))
  Graph.shortestOfResult graph starts (graph.breadthFirst sources)
    (Graph.breadthFirstCorrect graph sources (graph.Reached starts)
      (source member => Graph.reachedSources graph starts source 0 (List.memMap sources source member (other => (other, 0))))
      (Graph.reachedEdges graph starts) unit)

--| Some walk from one of the `sources` ends at `state`: it can be reached,
--| however much the walk costs.
def Graph.Reachable (graph: Graph s) (sources: List s) (state: s): Prop :=
  Exists s (source => Exists (List (s, Nat)) (path => (source ∈ sources) ∧ (graph.Walk source path state)))

--| The states reachable from `sources` (the sources themselves included),
--| whatever the edges cost: [`Graph.reachableIff`] says `contains` is
--| [`Graph.Reachable`]. It is the keys of breadth-first search
--| ([`Graph.breadthFirst`]), which ignores the costs and so does a set
--| operation or two per edge rather than Dijkstra's queue work.
def Graph.reachable [auto ord: Ord s] (graph: Graph s) (sources: List s): Set s :=
  (graph.breadthFirst sources).keySet

--| A walk from a state with a value in `result` ends at one, when each edge
--| out of a state with a value leads to one.
theorem Graph.valueAlong [auto ord: Ord s] (graph: Graph s) (result: Map s Nat)
    (closed: ∀ (state: s) (cost: Nat) => result.get state = Some cost → ∀ (next: s) (weight: Nat) => (next, weight) ∈ graph.edges state →
      Graph.Bound result (cost + 1) next):
    ∀ (start: s) => Exists Nat (cost => result.get start = Some cost) → ∀ (path: List (s, Nat)) (finish: s) => graph.Walk start path finish →
      Exists Nat (cost => result.get finish = Some cost)
  | start, has, [], finish, walked => rewrite <- walked in has
  | start, has, [(next, weight), ..rest], finish, (Both edge later) =>
    let (Witness cost got) := has
    let (Witness found (Both gotNext le)) := closed start cost got next weight edge
    Graph.valueAlong graph result closed next (Witness found gotNext) rest finish later

--| The states `Graph.reachable` returns are exactly those a walk from a
--| source ends at.
theorem Graph.reachableIff [auto ord: Ord s] (graph: Graph s) (sources: List s) (state: s):
    ((graph.reachable sources).contains state = True) ↔ graph.Reachable sources state :=
  let steps :=
    Graph.breadthFirstSteps graph sources (state cost => graph.Reachable sources state)
      (source member => Witness source (Witness [] (Both member rfl)))
      (state cost (Witness source (Witness path (Both member walked))) next weight edge =>
        Witness source (Witness (path ++ [(next, weight)]) (Both member (Graph.walkSnoc graph source path state walked next weight edge))))
  let (Both settledReach (Both sourcesBound closed)) := steps
  {
    forward = there =>
      let (Witness cost got) := Map.getOfContains _ state (Eq.trans (Eq.sym (Map.containsKeySet (graph.breadthFirst sources) state)) there)
      settledReach state cost got,
    backward = (Witness source (Witness path (Both inSources walked))) =>
      let (Witness start (Both got bound)) := sourcesBound source 0 (List.memMap sources source inSources (other => (other, 0)))
      let (Witness cost gotEnd) := Graph.valueAlong graph (graph.breadthFirst sources) closed source (Witness start got) path state walked
      Eq.trans (Map.containsKeySet (graph.breadthFirst sources) state) (Map.containsOfGet _ state cost gotEnd)
  }
