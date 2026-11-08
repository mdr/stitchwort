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
  listed: (state: s) → (next: s) → (weight: Nat) → (next, weight) ∈ edges state → next ∈ states
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
theorem Graph.walkAppend (graph: Graph s) (more: List (s, Nat)) (finish: s): (start: s) → (path: List (s, Nat)) → (middle: s) →
    graph.Walk start path middle → graph.Walk middle more finish → graph.Walk start (path ++ more) finish
  | start, [], middle, walked, after => rewrite walked in after
  | start, [(next, weight), ..rest], middle, (Both edge later), after => Both edge (Graph.walkAppend graph more finish next rest middle later after)

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
  ((state: s) → (cost: Nat) → result.get state = Some cost → reach state cost) ∧ (((source: s) → (start: Nat) → (source, start) ∈ sources → Graph.Bound result start source) ∧ ((state: s) → (cost: Nat) → result.get state = Some cost → (next: s) → (weight: Nat) → (next, weight) ∈ graph.edges state →
    Graph.Bound result (cost + weight) next))

--| Along any walk, a search's bound grows by no more than the walk's cost.
theorem Graph.boundAlong [auto ord: Ord s] (graph: Graph s) (result: Map s Nat)
    (closed: (state: s) → (cost: Nat) → result.get state = Some cost → (next: s) → (weight: Nat) → (next, weight) ∈ graph.edges state →
      Graph.Bound result (cost + weight) next):
    (start: s) → (cost: Nat) → Graph.Bound result cost start → (path: List (s, Nat)) → (finish: s) → graph.Walk start path finish →
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
  ((state: s) → (cost: Nat) → result.get state = Some cost → graph.Reached sources state cost) ∧ ((source: s) → (start: Nat) → (source, start) ∈ sources → (path: List (s, Nat)) → (state: s) → graph.Walk source path state →
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
    (grows: (state: s) → settled.contains state = True → more.contains state = True) (state: s) (member: state ∈ universe)
    (fresh: settled.contains state = False) (now: more.contains state = True): Graph.unsettledIn universe more < Graph.unsettledIn universe settled :=
  List.countLtMem universe (other => !more.contains other) (other => !settled.contains other)
    (other inside kept =>
      match there: settled.contains other with
        | True => rewrite grows other there at kept in kept
        | False => rfl)
    state member (rewrite fresh in rfl) (rewrite now in rfl)

-- Dijkstra's algorithm

--| Whether `total` is less than the cost `best` has for `state`; it is
--| when `best` has none.
def Graph.improves [auto ord: Ord s] (best: Map s Nat) (state: s) (total: Nat): Bool :=
  match best.get state with
    | None => True
    | Some known => total < known

--| A cost that doesn't improve is no less than one `best` has.
theorem Graph.improvesFalse [auto ord: Ord s] (best: Map s Nat) (state: s) (total: Nat) (no: Graph.improves best state total = False):
    Exists Nat (known => (best.get state = Some known) ∧ (known ≤ total)) :=
  match got: best.get state with
    | None => Void.exfalso (Bool.trueNotFalse no)
    | Some known => Witness known (Both rfl omega)

--| A cost that improves is less than any `best` has.
theorem Graph.improvesTrue [auto ord: Ord s] (best: Map s Nat) (state: s) (total: Nat) (yes: Graph.improves best state total = True)
    (known: Nat) (got: best.get state = Some known): total < known :=
  rewrite got at yes in omega

--| Each edge whose state it gets to for less than `best` has, at `cost`
--| plus the edge's: the state queued at that cost, and the cost kept in
--| `best`. A settled state is never queued again: `best` has it for no more
--| than its settled cost, which no later cost is below.
@[tailrec]
def Graph.relaxEdges [auto ord: Ord s] (cost: Nat): (edges: List (s, Nat)) → (queue: Set (Nat, s)) → (best: Map s Nat) → (Set (Nat, s), Map s Nat)
  | [], queue, best => (queue, best)
  | [(next, weight), ..rest], queue, best =>
    if Graph.improves best next (cost + weight) then Graph.relaxEdges cost rest (queue.insert (cost + weight, next)) (best.insert next (cost + weight))
    else Graph.relaxEdges cost rest queue best

--| Relaxing edges keeps what the queue had.
theorem Graph.relaxKeeps [auto ord: Ord s] (cost: Nat): (edges: List (s, Nat)) → (queue: Set (Nat, s)) → (best: Map s Nat) → (entry: (Nat, s)) →
    queue.contains entry = True → (Graph.relaxEdges cost edges queue best).fst.contains entry = True
  | [], queue, best, entry, there => there
  | [(next, weight), ..rest], queue, best, entry, there =>
    match better: Graph.improves best next (cost + weight) with
      | True =>
        Graph.relaxKeeps cost rest (queue.insert (cost + weight, next)) (best.insert next (cost + weight)) entry
          (Set.containsInsertMono queue (cost + weight, next) entry there)
      | False => Graph.relaxKeeps cost rest queue best entry there

--| Relaxing edges queues nothing but each edge's state at `cost` plus its
--| cost.
theorem Graph.relaxAdded [auto ord: Ord s] (cost: Nat): (edges: List (s, Nat)) → (queue: Set (Nat, s)) → (best: Map s Nat) → (total: Nat) → (state: s) →
    (Graph.relaxEdges cost edges queue best).fst.contains (total, state) = True →
    (queue.contains (total, state) = True) ∨ (Exists Nat (weight => ((state, weight) ∈ edges) ∧ (total = cost + weight)))
  | [], queue, best, total, state, there => Inl there
  | [(next, weight), ..rest], queue, best, total, state, there =>
    match better: Graph.improves best next (cost + weight) with
      | False =>
        match Graph.relaxAdded cost rest queue best total state there with
          | Inl old => Inl old
          | Inr (Witness found (Both member costs)) => Inr (Witness found (Both (Inr member) costs))
      | True =>
        match Graph.relaxAdded cost rest (queue.insert (cost + weight, next)) (best.insert next (cost + weight)) total state there with
          | Inr (Witness found (Both member costs)) => Inr (Witness found (Both (Inr member) costs))
          | Inl inserted =>
            match same: (total, state) == (cost + weight, next) with
              | True =>
                let equal := DecEq.sound same
                Inr (Witness weight (Both (Inl (Eq.cong (found => (found, weight)) (Eq.sym (Eq.cong Pair.snd equal)))) (Eq.cong Pair.fst equal)))
              | False =>
                Inl (Eq.trans (Eq.sym (Set.containsInsertOther queue (cost + weight, next) (total, state) (DecEq.soundFalse _ _ same))) inserted)

--| Each cost relaxing edges records in `best` was there before, or is
--| queued.
theorem Graph.relaxBest [auto ord: Ord s] (cost: Nat): (edges: List (s, Nat)) → (queue: Set (Nat, s)) → (best: Map s Nat) → (state: s) → (found: Nat) →
    (Graph.relaxEdges cost edges queue best).snd.get state = Some found →
    (best.get state = Some found) ∨ ((Graph.relaxEdges cost edges queue best).fst.contains (found, state) = True)
  | [], queue, best, state, found, got => Inl got
  | [(next, weight), ..rest], queue, best, state, found, got =>
    match better: Graph.improves best next (cost + weight) with
      | False => Graph.relaxBest cost rest queue best state found got
      | True =>
        let more := queue.insert (cost + weight, next)
        match Graph.relaxBest cost rest more (best.insert next (cost + weight)) state found got with
          | Inr queued => Inr queued
          | Inl inserted =>
            match Map.getInsertCases best next (cost + weight) state found inserted with
              | Inr old => Inl old
              | Inl (Both same costs) =>
                Inr
                  (rewrite same, costs in
                    Graph.relaxKeeps cost rest more (best.insert next (cost + weight)) (cost + weight, next)
                      (Set.containsInsert (cost + weight, next) queue))

--| Relaxing edges never raises a cost `best` has.
theorem Graph.relaxLowers [auto ord: Ord s] (cost: Nat): (edges: List (s, Nat)) → (queue: Set (Nat, s)) → (best: Map s Nat) → (state: s) → (known: Nat) →
    best.get state = Some known →
    Exists Nat (found => ((Graph.relaxEdges cost edges queue best).snd.get state = Some found) ∧ (found ≤ known))
  | [], queue, best, state, known, got => Witness known (Both got (Nat.leRefl known))
  | [(next, weight), ..rest], queue, best, state, known, got =>
    match better: Graph.improves best next (cost + weight) with
      | False => Graph.relaxLowers cost rest queue best state known got
      | True =>
        let more := queue.insert (cost + weight, next)
        let lowered := best.insert next (cost + weight)
        match same: state == next with
          | True =>
            let equal := DecEq.sound same
            let less := Graph.improvesTrue best next (cost + weight) better known (rewrite <- equal in got)
            let (Witness found (Both final le)) :=
              Graph.relaxLowers cost rest more lowered state (cost + weight) (rewrite equal in Map.getInsert next (cost + weight) best)
            Witness found (Both final (omega [le, less]))
          | False =>
            Graph.relaxLowers cost rest more lowered state known
              (Eq.trans (Map.getInsertOther next (cost + weight) state (DecEq.soundFalse _ _ same) best) got)

--| After relaxing edges, `best` has each edge's state for no more than
--| `cost` plus the edge's.
theorem Graph.relaxCovers [auto ord: Ord s] (cost: Nat): (edges: List (s, Nat)) → (queue: Set (Nat, s)) → (best: Map s Nat) → (next: s) → (weight: Nat) →
    (next, weight) ∈ edges →
    Exists Nat (found => ((Graph.relaxEdges cost edges queue best).snd.get next = Some found) ∧ (found ≤ cost + weight))
  | [], queue, best, next, weight, member => Void.exfalso member
  | [(first, firstWeight), ..rest], queue, best, next, weight, Inr later =>
    match better: Graph.improves best first (cost + firstWeight) with
      | False => Graph.relaxCovers cost rest queue best next weight later
      | True =>
        Graph.relaxCovers cost rest (queue.insert (cost + firstWeight, first)) (best.insert first (cost + firstWeight)) next weight later
  | [(first, firstWeight), ..rest], queue, best, next, weight, Inl here =>
    rewrite <- Eq.cong Pair.fst here, <- Eq.cong Pair.snd here in
      match better: Graph.improves best first (cost + firstWeight) with
        | False =>
          let (Witness known (Both got le)) := Graph.improvesFalse best first (cost + firstWeight) better
          let (Witness found (Both final lower)) := Graph.relaxLowers cost rest queue best first known got
          Witness found (Both final (omega [le, lower]))
        | True =>
          let (Witness found (Both final lower)) :=
            Graph.relaxLowers cost rest (queue.insert (cost + firstWeight, first)) (best.insert first (cost + firstWeight)) first
              (cost + firstWeight) (Map.getInsert first (cost + firstWeight) best)
          Witness found (Both final lower)

--| `Less` then anything is never a first comparison of `Greater`.
theorem Graph.notGreaterOfThen: (first: Ordering) → (second: Ordering) → Ordering.andThen first second = Less → first ≠ Greater
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
theorem Graph.startQueued [auto ord: Ord s] (graph: Graph s) (sources: List (s, Nat)) (cost: Nat) (state: s)
    (there: (Graph.relaxEdges 0 sources Set.empty Map.empty).fst.contains (cost, state) = True): state ∈ graph.universe sources :=
  match Graph.relaxAdded 0 sources Set.empty Map.empty cost state there with
    | Inl none => Void.exfalso (Bool.falseNotTrue none)
    | Inr (Witness start (Both member costs)) =>
      List.memAppendLeft state (sources.map Pair.fst) graph.states (List.memMap sources (state, start) member Pair.fst)

--| Every state queued after popping the least pair is in the universe.
theorem Graph.restQueued [auto ord: Ord s] (graph: Graph s) (sources: List (s, Nat)) (queue: Set (Nat, s)) (popped: (Nat, s))
    (rest: Set (Nat, s)) (found: queue.popMin = Some (popped, rest))
    (queued: (cost: Nat) → (state: s) → queue.contains (cost, state) = True → state ∈ graph.universe sources) (cost: Nat) (state: s)
    (there: rest.contains (cost, state) = True): state ∈ graph.universe sources :=
  let (Both least restIs) := Set.popMinSome queue popped rest found
  queued cost state (Set.containsOfRemove queue popped (cost, state) (rewrite restIs at there in there))

--| Every state queued after relaxing a state's edges is in the universe.
theorem Graph.relaxedQueued [auto ord: Ord s] (graph: Graph s) (sources: List (s, Nat)) (from: s) (fromCost: Nat) (rest: Set (Nat, s))
    (best: Map s Nat) (queued: (cost: Nat) → (state: s) → rest.contains (cost, state) = True → state ∈ graph.universe sources) (cost: Nat)
    (state: s) (there: (Graph.relaxEdges fromCost (graph.edges from) rest best).fst.contains (cost, state) = True): state ∈ graph.universe sources :=
  match Graph.relaxAdded fromCost (graph.edges from) rest best cost state there with
    | Inl inRest => queued cost state inRest
    | Inr (Witness weight (Both edge costs)) =>
      List.memAppendRight state (sources.map Pair.fst) graph.states (graph.listed from state weight edge)

--| Dijkstra's algorithm: `queue` holds (cost, state) pairs still to look at,
--| least first; `settled` the least cost found for each state settled so
--| far; `best` the least cost each state has been queued at. The least
--| pair, `popped` with the rest of the queue, settles its state, unless it
--| already is, and queues the states its edges get to for less than
--| `best` has. A pair left behind by a cheaper one for its state is
--| dropped when popped, its state settled by then.
@[tailrec]
def Graph.searchFrom [auto ord: Ord s] (graph: Graph s) (sources: List (s, Nat)) (queue: Set (Nat, s)) (settled: Map s Nat) (best: Map s Nat)
    (queued: (cost: Nat) → (state: s) → queue.contains (cost, state) = True → state ∈ graph.universe sources):
    (popped: Option ((Nat, s), Set (Nat, s))) → (found: queue.popMin = popped) → Map s Nat
    decreasing (Graph.unsettledIn (graph.universe sources) settled, queue.size)
  | None, found => settled
  | Some ((cost, state), rest), found =>
    let restQueued := Graph.restQueued graph sources queue (cost, state) rest found queued
    if fresh: settled.contains state = False then
      let relaxed := Graph.relaxEdges cost (graph.edges state) rest best
      Graph.searchFrom graph sources relaxed.fst (settled.insert state cost) relaxed.snd
        (Graph.relaxedQueued graph sources state cost rest best restQueued) relaxed.fst.popMin rfl
        [decreasing :=
          Nat.LexLess.First
            (Graph.unsettledFewer (graph.universe sources) settled (settled.insert state cost)
              (other there => Map.containsInsertKeeps settled state cost other there) state
              (queued cost state (Set.containsMin queue (cost, state) (And.left (Set.popMinSome queue (cost, state) rest found)))) fresh
              (Map.containsInsertSame settled state cost))]
    else
      Graph.searchFrom graph sources rest settled best restQueued rest.popMin rfl
        [decreasing := Nat.LexLess.Second rfl (Set.sizePopMin queue (cost, state) rest found)]

--| The least cost to each state reachable from one of the sources, each
--| given with the cost of starting there.
def Graph.distances [auto ord: Ord s] (graph: Graph s) (sources: List (s, Nat)): Map s Nat :=
  let start := Graph.relaxEdges 0 sources Set.empty Map.empty
  graph.searchFrom sources start.fst Map.empty start.snd (Graph.startQueued graph sources) start.fst.popMin rfl

--| A cost the search still has to account for: the state is queued for no
--| more, or settled for no more.
def Graph.Pending [auto ord: Ord s] (queue: Set (Nat, s)) (settled: Map s Nat) (cost: Nat) (state: s): Prop :=
  (Exists Nat (found => (found ≤ cost) ∧ (queue.contains (found, state) = True))) ∨ (Graph.Bound settled cost state)

--| A pending cost is pending for any larger one.
theorem Graph.pendingWeaken [auto ord: Ord s] (queue: Set (Nat, s)) (settled: Map s Nat) (cost: Nat) (more: Nat) (state: s)
    (pending: Graph.Pending queue settled cost state) (le: cost ≤ more): Graph.Pending queue settled more state :=
  match pending with
    | Inl (Witness found (Both below there)) => Inl (Witness found (Both (omega [below, le]) there))
    | Inr bound => Inr (Graph.boundWeaken settled cost more state bound le)

--| What holds at each step of the search.
--| Every queued pair and settled state is reached for its cost; each
--| source, each edge out of a settled state, and each cost in `best` is
--| pending; and nothing settled costs more than anything queued.
def Graph.SearchState [auto ord: Ord s] (graph: Graph s) (sources: List (s, Nat)) (reach: s → Nat → Prop) (queue: Set (Nat, s))
    (settled: Map s Nat) (best: Map s Nat): Prop :=
  ((cost: Nat) → (state: s) → queue.contains (cost, state) = True → reach state cost) ∧ (((state: s) → (cost: Nat) → settled.get state = Some cost → reach state cost) ∧ (((source: s) → (start: Nat) → (source, start) ∈ sources → Graph.Pending queue settled start source) ∧ (((state: s) → (cost: Nat) → settled.get state = Some cost → (next: s) → (weight: Nat) → (next, weight) ∈ graph.edges state →
    Graph.Pending queue settled (cost + weight) next) ∧ (((state: s) → (cost: Nat) → settled.get state = Some cost → (other: Nat) → (otherState: s) →
    queue.contains (other, otherState) = True → cost ≤ other) ∧ ((state: s) → (cost: Nat) → best.get state = Some cost → Graph.Pending queue settled cost state)))))

--| A pending cost stays pending when the queue keeps all but the popped
--| pair, the settled states stay, and the popped state is settled for no
--| more than the popped cost.
theorem Graph.pendingKept [auto ord: Ord s] (queue: Set (Nat, s)) (newQueue: Set (Nat, s)) (settled: Map s Nat) (newSettled: Map s Nat)
    (poppedCost: Nat) (poppedState: s) (poppedFound: Nat)
    (kept: (entry: (Nat, s)) → queue.contains entry = True → entry ≠ (poppedCost, poppedState) → newQueue.contains entry = True)
    (stays: (state: s) → (found: Nat) → settled.get state = Some found → newSettled.get state = Some found)
    (popped: newSettled.get poppedState = Some poppedFound) (cheaper: poppedFound ≤ poppedCost) (cost: Nat) (state: s)
    (pending: Graph.Pending queue settled cost state): Graph.Pending newQueue newSettled cost state :=
  match pending with
    | Inr (Witness found (Both got le)) => Inr (Witness found (Both (stays state found got) le))
    | Inl (Witness found (Both below there)) =>
      match same: (found, state) == (poppedCost, poppedState) with
        | True =>
          let equal := DecEq.sound same
          let costs: found = poppedCost := Eq.cong Pair.fst equal
          Inr (Witness poppedFound (Both (rewrite Eq.cong Pair.snd equal in popped) (omega [costs, cheaper, below])))
        | False => Inl (Witness found (Both below (kept (found, state) there (DecEq.soundFalse _ _ same))))

--| With nothing queued, a pending cost is a bound.
theorem Graph.boundOfPending [auto ord: Ord s] (queue: Set (Nat, s)) (settled: Map s Nat) (empty: queue.popMin = None) (cost: Nat) (state: s)
    (pending: Graph.Pending queue settled cost state): Graph.Bound settled cost state :=
  match pending with
    | Inr bound => bound
    | Inl (Witness found (Both below there)) =>
      Void.exfalso (Bool.falseNotTrue (Eq.trans (Eq.sym (Set.missingOfMinNone queue (Set.popMinNone queue empty) (found, state))) there))

--| Dropping a popped pair whose state is settled keeps the search state.
theorem Graph.skipKeeps [auto ord: Ord s] (graph: Graph s) (sources: List (s, Nat)) (reach: s → Nat → Prop) (queue: Set (Nat, s))
    (settled: Map s Nat) (best: Map s Nat) (cost: Nat) (state: s) (found: queue.min = Some (cost, state)) (taken: settled.contains state = True)
    (invariant: Graph.SearchState graph sources reach queue settled best):
    Graph.SearchState graph sources reach (queue.remove (cost, state)) settled best :=
  let (Both queuedReach (Both settledReached (Both sourcesPending (Both edgesPending (Both ordered bestPending))))) := invariant
  let inQueue := Set.containsMin queue (cost, state) found
  Exists.elim (Map.getOfContains settled state taken) (settledCost got =>
    let cheaper := ordered state settledCost got cost state inQueue
    let keep := Graph.pendingKept queue (queue.remove (cost, state)) settled settled cost state settledCost
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
theorem Graph.settleKeeps [auto ord: Ord s] (graph: Graph s) (sources: List (s, Nat)) (reach: s → Nat → Prop)
    (edgesReach: (state: s) → (cost: Nat) → reach state cost → (next: s) → (weight: Nat) → (next, weight) ∈ graph.edges state →
      reach next (cost + weight))
    (queue: Set (Nat, s)) (settled: Map s Nat) (best: Map s Nat) (cost: Nat) (state: s) (found: queue.min = Some (cost, state))
    (fresh: settled.contains state = False) (invariant: Graph.SearchState graph sources reach queue settled best):
    Graph.SearchState graph sources reach (Graph.relaxEdges cost (graph.edges state) (queue.remove (cost, state)) best).fst (settled.insert state cost)
      (Graph.relaxEdges cost (graph.edges state) (queue.remove (cost, state)) best).snd :=
  let (Both queuedReach (Both settledReached (Both sourcesPending (Both edgesPending (Both ordered bestPending))))) := invariant
  let rest := queue.remove (cost, state)
  let relaxed := Graph.relaxEdges cost (graph.edges state) rest best
  let inQueue := Set.containsMin queue (cost, state) found
  let reached := queuedReach cost state inQueue
  let poppedGot: (settled.insert state cost).get state = Some cost := Map.getInsert state cost settled
  let keep := Graph.pendingKept queue relaxed.fst settled (settled.insert state cost) cost state cost
    (entry there apart =>
      Graph.relaxKeeps cost (graph.edges state) rest best entry (Eq.trans (Set.containsRemoveOther queue (cost, state) entry apart) there))
    (other value got => Map.getInsertKeeps settled state cost fresh other value got) poppedGot (Nat.leRefl cost)
  let atLeast: (other: Nat) → (otherState: s) → relaxed.fst.contains (other, otherState) = True → cost ≤ other :=
    other otherState there =>
      match Graph.relaxAdded cost (graph.edges state) rest best other otherState there with
        | Inl inRest => Graph.minLeast queue cost state found other otherState (Set.containsOfRemove queue (cost, state) (other, otherState) inRest)
        | Inr (Witness weight (Both edge costs)) => rewrite costs in omega
  let newBest: (other: s) → (otherCost: Nat) → relaxed.snd.get other = Some otherCost →
      Graph.Pending relaxed.fst (settled.insert state cost) otherCost other :=
    other otherCost got =>
      match Graph.relaxBest cost (graph.edges state) rest best other otherCost got with
        | Inl old => keep otherCost other (bestPending other otherCost old)
        | Inr queued => Inl (Witness otherCost (Both (Nat.leRefl otherCost) queued))
  Both
    (other otherState there =>
      match Graph.relaxAdded cost (graph.edges state) rest best other otherState there with
        | Inl inRest => queuedReach other otherState (Set.containsOfRemove queue (cost, state) (other, otherState) inRest)
        | Inr (Witness weight (Both edge costs)) => rewrite costs in edgesReach state cost reached otherState weight edge)
    (Both
      (other otherCost got =>
        match Map.getInsertCases settled state cost other otherCost got with
          | Inl (Both same costs) => rewrite same, costs in reached
          | Inr old => settledReached other otherCost old)
      (Both (source start member => keep start source (sourcesPending source start member))
        (Both
          (from fromCost got next weight edge =>
            match Map.getInsertCases settled state cost from fromCost got with
              | Inl (Both same costs) =>
                let (Witness bestCost (Both bestGot le)) :=
                  Graph.relaxCovers cost (graph.edges state) rest best next weight (rewrite <- same in edge)
                rewrite costs in
                  Graph.pendingWeaken relaxed.fst (settled.insert state cost) bestCost (cost + weight) next (newBest next bestCost bestGot) le
              | Inr old => keep (fromCost + weight) next (edgesPending from fromCost old next weight edge))
          (Both
            (from fromCost got other otherState there =>
              match Map.getInsertCases settled state cost from fromCost got with
                | Inl (Both same costs) => rewrite costs in atLeast other otherState there
                | Inr old => omega [ordered from fromCost old cost state inQueue, atLeast other otherState there])
            newBest))))

--| The search returns what `SearchResult` says, from any search state.
theorem Graph.searchFromCorrect [auto ord: Ord s] (graph: Graph s) (sources: List (s, Nat)) (reach: s → Nat → Prop)
    (edgesReach: (state: s) → (cost: Nat) → reach state cost → (next: s) → (weight: Nat) → (next, weight) ∈ graph.edges state →
      reach next (cost + weight))
    (queue: Set (Nat, s)) (settled: Map s Nat) (best: Map s Nat)
    (queued: (cost: Nat) → (state: s) → queue.contains (cost, state) = True → state ∈ graph.universe sources):
    (popped: Option ((Nat, s), Set (Nat, s))) → (found: queue.popMin = popped) → Graph.SearchState graph sources reach queue settled best →
      Graph.SearchResult graph sources reach (graph.searchFrom sources queue settled best queued popped found)
    decreasing (Graph.unsettledIn (graph.universe sources) settled, queue.size)
  | None, found, invariant =>
    rewrite Graph.searchFrom.eq1 graph sources queue settled best queued found in
      let (Both queuedReach (Both settledReached (Both sourcesPending (Both edgesPending others)))) := invariant
      Both settledReached
        (Both (source start member => Graph.boundOfPending queue settled found start source (sourcesPending source start member))
          (from fromCost got next weight edge =>
            Graph.boundOfPending queue settled found (fromCost + weight) next (edgesPending from fromCost got next weight edge)))
  | Some ((cost, state), rest), found, invariant =>
    let (Both least restIs) := Set.popMinSome queue (cost, state) rest found
    let restQueued := Graph.restQueued graph sources queue (cost, state) rest found queued
    match taken: settled.contains state with
      | True =>
        rewrite Graph.searchFrom.eq2.ifFalse graph sources queue settled best queued cost state rest found taken in
          Graph.searchFromCorrect graph sources reach edgesReach rest settled best restQueued rest.popMin rfl
            (rewrite restIs in Graph.skipKeeps graph sources reach queue settled best cost state least taken invariant)
            [decreasing := Nat.LexLess.Second rfl (Set.sizePopMin queue (cost, state) rest found)]
      | False =>
        let relaxed := Graph.relaxEdges cost (graph.edges state) rest best
        rewrite Graph.searchFrom.eq2.ifTrue graph sources queue settled best queued cost state rest found taken in
          Graph.searchFromCorrect graph sources reach edgesReach relaxed.fst (settled.insert state cost) relaxed.snd
            (Graph.relaxedQueued graph sources state cost rest best restQueued) relaxed.fst.popMin rfl
            (rewrite restIs in Graph.settleKeeps graph sources reach edgesReach queue settled best cost state least taken invariant)
            [decreasing :=
              Nat.LexLess.First
                (Graph.unsettledFewer (graph.universe sources) settled (settled.insert state cost)
                  (other there => Map.containsInsertKeeps settled state cost other there) state
                  (queued cost state (Set.containsMin queue (cost, state) least)) taken (Map.containsInsertSame settled state cost))]

--| Dijkstra's search returns what `SearchResult` says, for any `reach` that
--| holds at each source for its starting cost and along each edge.
theorem Graph.distancesCorrect [auto ord: Ord s] (graph: Graph s) (sources: List (s, Nat)) (reach: s → Nat → Prop)
    (sourcesReach: (source: s) → (start: Nat) → (source, start) ∈ sources → reach source start)
    (edgesReach: (state: s) → (cost: Nat) → reach state cost → (next: s) → (weight: Nat) → (next, weight) ∈ graph.edges state →
      reach next (cost + weight)):
    Graph.SearchResult graph sources reach (graph.distances sources) :=
  let start := Graph.relaxEdges 0 sources Set.empty Map.empty
  let startBest: (state: s) → (cost: Nat) → start.snd.get state = Some cost → Graph.Pending start.fst Map.empty cost state :=
    state cost got =>
      match Graph.relaxBest 0 sources Set.empty Map.empty state cost got with
        | Inl none => Void.exfalso (Option.noneNotSome cost none)
        | Inr queued => Inl (Witness cost (Both (Nat.leRefl cost) queued))
  let initial: Graph.SearchState graph sources reach start.fst Map.empty start.snd :=
    Both
      (cost state there =>
        match Graph.relaxAdded 0 sources Set.empty Map.empty cost state there with
          | Inl none => Void.exfalso (Bool.falseNotTrue none)
          | Inr (Witness begin (Both member costs)) =>
            let same: cost = begin := omega
            rewrite same in sourcesReach state begin member)
      (Both (state cost got => Void.exfalso (Option.noneNotSome cost got))
        (Both
          (source begin member =>
            let (Witness found (Both got le)) := Graph.relaxCovers 0 sources Set.empty Map.empty source begin member
            Graph.pendingWeaken start.fst Map.empty found begin source (startBest source found got) (omega [le]))
          (Both (state cost got => Void.exfalso (Option.noneNotSome cost got))
            (Both (state cost got => Void.exfalso (Option.noneNotSome cost got)) startBest))))
  Graph.searchFromCorrect graph sources reach edgesReach start.fst Map.empty start.snd (Graph.startQueued graph sources) start.fst.popMin rfl initial

--| Each cost Dijkstra's search finds is a walk's from a source, and no walk
--| from a source costs less.
theorem Graph.distancesShortest [auto ord: Ord s] (graph: Graph s) (sources: List (s, Nat)): Graph.Shortest graph sources (graph.distances sources) :=
  Graph.shortestOfResult graph sources (graph.distances sources)
    (Graph.distancesCorrect graph sources (graph.Reached sources) (Graph.reachedSources graph sources) (Graph.reachedEdges graph sources))

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
theorem Graph.visitGrows [auto ord: Ord s] (depth: Nat): (edges: List (s, Nat)) → (settled: Map s Nat) → (next: List s) → (state: s) →
    (cost: Nat) → settled.get state = Some cost → (Graph.visitEdges depth edges settled next).fst.get state = Some cost
  | [], settled, next, state, cost, got => got
  | [(target, weight), ..rest], settled, next, state, cost, got =>
    match there: settled.contains target with
      | True => Graph.visitGrows depth rest settled next state cost got
      | False =>
        Graph.visitGrows depth rest (settled.insert target depth) [target, ..next] state cost
          (Map.getInsertKeeps settled target depth there state cost got)

--| Visiting edges keeps what was on the list on it.
theorem Graph.visitListed [auto ord: Ord s] (depth: Nat): (edges: List (s, Nat)) → (settled: Map s Nat) → (next: List s) → (state: s) →
    state ∈ next → state ∈ (Graph.visitEdges depth edges settled next).snd
  | [], settled, next, state, member => member
  | [(target, weight), ..rest], settled, next, state, member =>
    match there: settled.contains target with
      | True => Graph.visitListed depth rest settled next state member
      | False => Graph.visitListed depth rest (settled.insert target depth) [target, ..next] state (Inr member)

--| What visiting edges settles anew is at `depth`, and put on the list.
theorem Graph.visitNew [auto ord: Ord s] (depth: Nat): (edges: List (s, Nat)) → (settled: Map s Nat) → (next: List s) → (state: s) →
    (cost: Nat) → (Graph.visitEdges depth edges settled next).fst.get state = Some cost →
    (settled.get state = Some cost) ∨ ((cost = depth) ∧ ((state ∈ (Graph.visitEdges depth edges settled next).snd) ∧ (Exists Nat (weight => (state, weight) ∈ edges))))
  | [], settled, next, state, cost, got => Inl got
  | [(target, weight), ..rest], settled, next, state, cost, got =>
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
theorem Graph.visitAdded [auto ord: Ord s] (depth: Nat): (edges: List (s, Nat)) → (settled: Map s Nat) → (next: List s) → (state: s) →
    state ∈ (Graph.visitEdges depth edges settled next).snd →
    (state ∈ next) ∨ ((settled.contains state = False) ∧ (((Graph.visitEdges depth edges settled next).fst.get state = Some depth) ∧ (Exists Nat (weight => (state, weight) ∈ edges))))
  | [], settled, next, state, member => Inl member
  | [(target, weight), ..rest], settled, next, state, member =>
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
theorem Graph.visitCovers [auto ord: Ord s] (depth: Nat): (edges: List (s, Nat)) → (settled: Map s Nat) → (next: List s) → (state: s) →
    (weight: Nat) → (state, weight) ∈ edges → (Graph.visitEdges depth edges settled next).fst.contains state = True
  | [], settled, next, state, weight, member => Void.exfalso member
  | [(target, targetWeight), ..rest], settled, next, state, weight, member =>
    let settles: (more: Map s Nat) → (added: List s) → more.contains state = True →
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
  ((state: s) → (cost: Nat) → settled.get state = Some cost → (reach state cost) ∧ (cost ≤ depth)) ∧ (((state: s) → (state ∈ frontier) ↔ (settled.get state = Some depth)) ∧ (((state: s) → (cost: Nat) → settled.get state = Some cost → cost < depth → (next: s) → (weight: Nat) →
    (next, weight) ∈ graph.edges state → Graph.Bound settled (cost + 1) next) ∧ ((source: s) → source ∈ sources → Graph.Bound settled 0 source)))

--| A bound survives visiting.
theorem Graph.visitBound [auto ord: Ord s] (depth: Nat) (edges: List (s, Nat)) (settled: Map s Nat) (next: List s) (cost: Nat) (state: s)
    (bound: Graph.Bound settled cost state): Graph.Bound (Graph.visitEdges depth edges settled next).fst cost state :=
  Exists.elim bound (found both => Witness found (Both (Graph.visitGrows depth edges settled next state found (And.left both)) (And.right both)))

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
    (invariant: Graph.BreadthState graph sources reach depth settled frontier)
    (unit: (state: s) → (next: s) → (weight: Nat) → (next, weight) ∈ graph.edges state → weight = 1):
    Graph.SearchResult graph (sources.map (source => (source, 0))) reach more :=
  let (Both settledReach (Both atFrontier (Both closedBelow sourcesBound))) := invariant
  let edges := frontier.flatMap graph.edges
  let moreIs: (Graph.visitEdges (depth + 1) edges settled []).fst = more := Eq.cong Pair.fst found
  let nextIs: (Graph.visitEdges (depth + 1) edges settled []).snd = [] := Eq.cong Pair.snd found
  let old: (state: s) → (cost: Nat) → more.get state = Some cost → settled.get state = Some cost :=
    state cost got =>
      match Graph.visitNew (depth + 1) edges settled [] state cost (rewrite moreIs in got) with
        | Inl was => was
        | Inr (Both costs (Both listed others)) => Void.exfalso (rewrite nextIs at listed in listed)
  let grows: (cost: Nat) → (state: s) → Graph.Bound settled cost state → Graph.Bound more cost state :=
    cost state bound => rewrite <- moreIs in Graph.visitBound (depth + 1) edges settled [] cost state bound
  Both (state cost got => And.left (settledReach state cost (old state cost got)))
    (Both
      (source start member =>
        List.anyElim (other => (other, 0) = (source, start)) (Graph.Bound more start source) sources
          (List.memMapAny sources (source => (source, 0)) (source, start) member) (other inSources same =>
            rewrite <- Eq.cong Pair.snd same, <- Eq.cong Pair.fst same in grows 0 other (sourcesBound other inSources)))
      (state cost got next weight edge =>
        let was := old state cost got
        rewrite unit state next weight edge in
          match Nat.decLessThan cost depth with
            | Yes below => grows (cost + 1) next (closedBelow state cost was below next weight edge)
            | No notBelow =>
              let atDepth: cost = depth := omega [And.right (settledReach state cost was), notBelow]
              let inFrontier := (atFrontier state).backward (rewrite <- atDepth in was)
              rewrite atDepth, <- moreIs in Graph.frontierClosed graph sources reach depth settled frontier invariant state inFrontier next weight edge))

--| One level keeps the search state.
theorem Graph.breadthKeeps [auto ord: Ord s] (graph: Graph s) (sources: List s) (reach: s → Nat → Prop)
    (edgesReach: (state: s) → (cost: Nat) → reach state cost → (next: s) → (weight: Nat) → (next, weight) ∈ graph.edges state →
      reach next (cost + weight))
    (unit: (state: s) → (next: s) → (weight: Nat) → (next, weight) ∈ graph.edges state → weight = 1) (depth: Nat) (settled: Map s Nat)
    (frontier: List s) (more: Map s Nat) (nextFrontier: List s) (found: graph.visitFrontier (depth + 1) frontier settled = (more, nextFrontier))
    (invariant: Graph.BreadthState graph sources reach depth settled frontier): Graph.BreadthState graph sources reach (depth + 1) more nextFrontier :=
  let (Both settledReach (Both atFrontier (Both closedBelow sourcesBound))) := invariant
  let edges := frontier.flatMap graph.edges
  let moreIs: (Graph.visitEdges (depth + 1) edges settled []).fst = more := Eq.cong Pair.fst found
  let nextIs: (Graph.visitEdges (depth + 1) edges settled []).snd = nextFrontier := Eq.cong Pair.snd found
  let grows: (cost: Nat) → (state: s) → Graph.Bound settled cost state → Graph.Bound more cost state :=
    cost state bound => rewrite <- moreIs in Graph.visitBound (depth + 1) edges settled [] cost state bound
  -- What is settled now was settled before, or is new at `depth + 1` and
  -- on the next frontier.
  let origin: (state: s) → (cost: Nat) → more.get state = Some cost →
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
              rewrite costs in Both (rewrite unit from state weight fromEdge at reached) (Nat.leRefl (depth + 1))))
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
              match Nat.decLessThan cost depth with
                | Yes lower => grows (cost + 1) next (closedBelow state cost old lower next weight edge)
                | No notLower =>
                  let atDepth: cost = depth := omega [below, notLower]
                  let inFrontier := (atFrontier state).backward (rewrite <- atDepth in old)
                  rewrite atDepth, <- moreIs in Graph.frontierClosed graph sources reach depth settled frontier invariant state inFrontier next weight edge)
        (source member => grows 0 source (sourcesBound source member))))

--| The search returns what `SearchResult` says, from any search state.
theorem Graph.breadthFromCorrect [auto ord: Ord s] (graph: Graph s) (sources: List s) (reach: s → Nat → Prop)
    (edgesReach: (state: s) → (cost: Nat) → reach state cost → (next: s) → (weight: Nat) → (next, weight) ∈ graph.edges state →
      reach next (cost + weight))
    (unit: (state: s) → (next: s) → (weight: Nat) → (next, weight) ∈ graph.edges state → weight = 1) (depth: Nat) (settled: Map s Nat)
    (frontier: List s):
    (visited: (Map s Nat, List s)) → (found: graph.visitFrontier (depth + 1) frontier settled = visited) →
      Graph.BreadthState graph sources reach depth settled frontier →
      Graph.SearchResult graph (sources.map (source => (source, 0))) reach (graph.breadthFrom depth settled frontier visited found)
    decreasing Graph.unsettledIn graph.states settled
  | (more, []), found, invariant =>
    rewrite Graph.breadthDone graph depth settled frontier more found in
      Graph.breadthDoneCorrect graph sources reach depth settled frontier more found invariant unit
  | (more, [first, ..rest]), found, invariant =>
    rewrite Graph.breadthStep graph depth settled frontier more first rest found in
      Graph.breadthFromCorrect graph sources reach edgesReach unit (depth + 1) more [first, ..rest]
        (graph.visitFrontier (depth + 1 + 1) [first, ..rest] more) rfl
        (Graph.breadthKeeps graph sources reach edgesReach unit depth settled frontier more [first, ..rest] found invariant)
        [decreasing := Graph.visitFewer graph (depth + 1) frontier settled more first rest found]

--| Breadth-first search returns what `SearchResult` says, for a graph whose
--| edges each cost 1 and any `reach` that holds at each source for 0 and
--| along each edge.
theorem Graph.breadthFirstCorrect [auto ord: Ord s] (graph: Graph s) (sources: List s) (reach: s → Nat → Prop)
    (sourcesReach: (source: s) → source ∈ sources → reach source 0)
    (edgesReach: (state: s) → (cost: Nat) → reach state cost → (next: s) → (weight: Nat) → (next, weight) ∈ graph.edges state →
      reach next (cost + weight))
    (unit: (state: s) → (next: s) → (weight: Nat) → (next, weight) ∈ graph.edges state → weight = 1):
    Graph.SearchResult graph (sources.map (source => (source, 0))) reach (graph.breadthFirst sources) :=
  let edges := sources.map (source => (source, 0))
  let start := Graph.visitEdges 0 edges Map.empty []
  let fromSource: (state: s) → (weight: Nat) → (state, weight) ∈ edges → state ∈ sources :=
    state weight member =>
      List.anyElim (source => (source, 0) = (state, weight)) (state ∈ sources) sources (List.memMapAny sources (source => (source, 0)) (state, weight) member)
        (source inSources same => rewrite <- Eq.cong Pair.fst same in inSources)
  let origin: (state: s) → (cost: Nat) → start.fst.get state = Some cost →
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
  Graph.breadthFromCorrect graph sources reach edgesReach unit 0 start.fst start.snd (graph.visitFrontier (0 + 1) start.snd start.fst) rfl initial

--| On a graph whose edges each cost 1, each count breadth-first search finds
--| is a walk's from a source, and no walk from a source has fewer edges.
theorem Graph.breadthFirstShortest [auto ord: Ord s] (graph: Graph s) (sources: List s)
    (unit: (state: s) → (next: s) → (weight: Nat) → (next, weight) ∈ graph.edges state → weight = 1):
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
--| [`Graph.Reachable`]. It runs Dijkstra's search ([`Graph.distances`]) with
--| every source starting at 0, so it costs about an edge-count of set
--| operations; [`Graph.breadthFirst`] is the faster search for the fewest
--| edges, but is only proved for edges that each cost 1.
def Graph.reachable [auto ord: Ord s] (graph: Graph s) (sources: List s): Set s :=
  (graph.distances (sources.map (source => (source, 0)))).keySet

--| The states `Graph.reachable` returns are exactly those a walk from a
--| source ends at.
theorem Graph.reachableIff [auto ord: Ord s] (graph: Graph s) (sources: List s) (state: s):
    ((graph.reachable sources).contains state = True) ↔ graph.Reachable sources state :=
  let starts := sources.map (source => (source, 0))
  let (Both found complete) := Graph.distancesShortest graph starts
  {
    forward = there =>
      let (Witness cost got) := Map.getOfContains _ state (Eq.trans (Eq.sym (Map.containsKeySet (graph.distances starts) state)) there)
      let (Witness source (Witness start (Witness path (Both member (Both walked costs))))) := found state cost got
      let (Witness origin (Both inSources same)) := List.memMapElim (source => (source, 0)) (source, start) sources member
      Witness source (Witness path (Both (rewrite <- Eq.cong Pair.fst same in inSources) walked)),
    backward = (Witness source (Witness path (Both inSources walked))) =>
      let (Witness cost (Both got bound)) := complete source 0 (List.memMap sources source inSources (other => (other, 0))) path state walked
      Eq.trans (Map.containsKeySet (graph.distances starts) state) (Map.containsOfGet _ state cost got)
  }
