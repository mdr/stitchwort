-- Shortest paths in a graph given by each state's edges and their costs:
-- Dijkstra's algorithm (`Graph.distances`), and breadth-first search with a
-- plain queue for graphs whose edges each cost 1 (`Graph.breadthFirst`).
--
-- Both are proved against one spec, `Graph.SearchResult`: each state found
-- is reached for its cost, by whatever notion of reaching the caller gives,
-- each source is found for no more than its starting cost, and each edge
-- out of a found state leads to one found for no more than the two costs
-- together. With reaching taken as walking the graph's edges from a source
-- (`Graph.Reached`), that is `Graph.Shortest`: each cost found is a walk's,
-- and no walk costs less (`Graph.distancesShortest`,
-- `Graph.breadthFirstShortest`). `Graph.boundAlong` turns the spec into
-- bounds along any walk, for proofs about a program's own paths.
--
-- Both searches end without fuel because every edge leads to one of the
-- graph's listed `states`: each step settles one more of them, or shrinks
-- the queue.

-- A graph for a shortest-path search: each state's edges, with their costs,
-- and a list of states that every edge leads to.
type Graph (s: Type) = {
  edges: s → List (s, Nat),
  states: List s,
  listed: (state: s) → (next: s) → (weight: Nat) → (next, weight) ∈ edges state → next ∈ states
}

-- Walks

-- Edges followed from `start`, each one of the edges of the state before
-- it, ending at `finish`.
def Graph.Walk (graph: Graph s) (start: s): List (s, Nat) → s → Prop
  | Nil, finish => start = finish
  | Cons (next, weight) rest, finish => And ((next, weight) ∈ graph.edges start) (graph.Walk next rest finish)

-- What a walk's edges cost together.
def Graph.cost (path: List (s, Nat)): Nat := path.sumBy Pair.snd

theorem Graph.costNil: Graph.cost (Nil: List (s, Nat)) = 0 := rfl

theorem Graph.costCons (next: s) (weight: Nat) (rest: List (s, Nat)): Graph.cost (Cons (next, weight) rest) = weight + Graph.cost rest :=
  List.sumByCons rest (next, weight) Pair.snd

theorem Graph.costAppend (path: List (s, Nat)) (more: List (s, Nat)): Graph.cost (path ++ more) = Graph.cost path + Graph.cost more :=
  List.sumByAppend path more Pair.snd

-- A walk, then another from where it ends.
theorem Graph.walkAppend (graph: Graph s) (more: List (s, Nat)) (finish: s): (start: s) → (path: List (s, Nat)) → (middle: s) →
    graph.Walk start path middle → graph.Walk middle more finish → graph.Walk start (path ++ more) finish
  | start, Nil, middle, walked, after => rewrite walked in after
  | start, Cons (next, weight) rest, middle, (Both edge later), after => Both edge (Graph.walkAppend graph more finish next rest middle later after)

-- A walk, then one more edge.
theorem Graph.walkSnoc (graph: Graph s) (start: s) (path: List (s, Nat)) (middle: s) (walked: graph.Walk start path middle) (next: s) (weight: Nat)
    (edge: (next, weight) ∈ graph.edges middle): graph.Walk start (path ++ [(next, weight)]) next :=
  Graph.walkAppend graph [(next, weight)] next start path middle walked (Both edge rfl)

-- Some walk from a source ends at `state`, costing `cost` with the
-- source's starting cost.
def Graph.Reached (graph: Graph s) (sources: List (s, Nat)) (state: s) (cost: Nat): Prop :=
  Exists s (source =>
    Exists Nat (start =>
      Exists (List (s, Nat)) (path => And ((source, start) ∈ sources) (And (graph.Walk source path state) (start + Graph.cost path = cost)))))

theorem Graph.reachedSources (graph: Graph s) (sources: List (s, Nat)) (source: s) (start: Nat) (member: (source, start) ∈ sources):
    graph.Reached sources source start :=
  Witness source (Witness start (Witness Nil (Both member (Both rfl (omega: start + 0 = start)))))

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
                  (rewrite Graph.costAppend path [(next, weight)], Graph.costCons next weight Nil, Graph.costNil [s := s] in omega [costs]))))))))

-- The spec

-- `state` is settled for no more than `cost`.
def Graph.Bound [auto ord: Ord s] (settled: Map s Nat) (cost: Nat) (state: s): Prop :=
  Exists Nat (found => And (settled.get state = Some found) (found ≤ cost))

-- A bound still holds for a larger cost.
theorem Graph.boundWeaken [auto ord: Ord s] (settled: Map s Nat) (cost: Nat) (more: Nat) (state: s) (bound: Graph.Bound settled cost state)
    (le: cost ≤ more): Graph.Bound settled more state :=
  Exists.elim bound (found both => Witness found (Both (And.left both) (omega [And.right both, le])))

-- What a search returns, for a `reach` that holds at the sources and along
-- every edge: each settled state reached for its cost, each source settled
-- for no more than its starting cost, and each edge out of a settled state
-- leading to one settled for no more than the two together.
def Graph.SearchResult [auto ord: Ord s] (graph: Graph s) (sources: List (s, Nat)) (reach: s → Nat → Prop) (result: Map s Nat): Prop :=
  And ((state: s) → (cost: Nat) → result.get state = Some cost → reach state cost)
    (And ((source: s) → (start: Nat) → (source, start) ∈ sources → Graph.Bound result start source)
      ((state: s) → (cost: Nat) → result.get state = Some cost → (next: s) → (weight: Nat) → (next, weight) ∈ graph.edges state →
        Graph.Bound result (cost + weight) next))

-- Along any walk, a search's bound grows by no more than the walk's cost.
theorem Graph.boundAlong [auto ord: Ord s] (graph: Graph s) (result: Map s Nat)
    (closed: (state: s) → (cost: Nat) → result.get state = Some cost → (next: s) → (weight: Nat) → (next, weight) ∈ graph.edges state →
      Graph.Bound result (cost + weight) next):
    (start: s) → (cost: Nat) → Graph.Bound result cost start → (path: List (s, Nat)) → (finish: s) → graph.Walk start path finish →
      Graph.Bound result (cost + Graph.cost path) finish
  | start, cost, bound, Nil, finish, walked => rewrite <- walked in Graph.boundWeaken result cost (cost + Graph.cost (Nil: List (s, Nat))) start bound (omega)
  | start, cost, bound, Cons (next, weight) rest, finish, (Both edge later) =>
    Exists.elim bound (found both =>
      let stepped := closed start found (And.left both) next weight edge
      let along := Graph.boundAlong graph result closed next (cost + weight)
        (Graph.boundWeaken result (found + weight) (cost + weight) next stepped (omega [And.right both])) rest finish later
      Graph.boundWeaken result (cost + weight + Graph.cost rest) (cost + Graph.cost (Cons (next, weight) rest)) finish along
        (rewrite Graph.costCons next weight rest in omega))

-- Each cost found is a walk's from a source, and no walk from a source
-- costs less.
def Graph.Shortest [auto ord: Ord s] (graph: Graph s) (sources: List (s, Nat)) (result: Map s Nat): Prop :=
  And ((state: s) → (cost: Nat) → result.get state = Some cost → graph.Reached sources state cost)
    ((source: s) → (start: Nat) → (source, start) ∈ sources → (path: List (s, Nat)) → (state: s) → graph.Walk source path state →
      Graph.Bound result (start + Graph.cost path) state)

theorem Graph.shortestOfResult [auto ord: Ord s] (graph: Graph s) (sources: List (s, Nat)) (result: Map s Nat)
    (correct: Graph.SearchResult graph sources (graph.Reached sources) result): Graph.Shortest graph sources result :=
  let (Both reachedAll (Both sourcesBound closed)) := correct
  Both reachedAll
    (source start member path state walked => Graph.boundAlong graph result closed source start (sourcesBound source start member) path state walked)

-- The states of `universe` not settled yet.
def Graph.unsettledIn [auto ord: Ord s] (universe: List s) (settled: Map s Nat): Nat := universe.count (state => !settled.contains state)

-- Settling more, including a state of `universe` not settled before,
-- leaves fewer unsettled.
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

-- The queue with each edge's state added, at `cost` plus the edge's.
def Graph.pushEdges [auto ord: Ord s] (cost: Nat): (edges: List (s, Nat)) → (queue: Set (Nat, s)) → Set (Nat, s)
  | Nil, queue => queue
  | Cons (next, weight) rest, queue => Graph.pushEdges cost rest (queue.insert (cost + weight, next))

-- Pushing edges keeps what the queue had...
theorem Graph.containsPushedKeeps [auto ord: Ord s] (cost: Nat): (edges: List (s, Nat)) → (queue: Set (Nat, s)) → (entry: (Nat, s)) →
    queue.contains entry = True → (Graph.pushEdges cost edges queue).contains entry = True
  | Nil, queue, entry, there => there
  | Cons (next, weight) rest, queue, entry, there =>
    Graph.containsPushedKeeps cost rest (queue.insert (cost + weight, next)) entry (Set.containsInsertMono queue (cost + weight, next) entry there)

-- ...adds each edge's state at `cost` plus its cost...
theorem Graph.containsPushedEdge [auto ord: Ord s] (cost: Nat): (edges: List (s, Nat)) → (queue: Set (Nat, s)) → (next: s) → (weight: Nat) →
    (next, weight) ∈ edges → (Graph.pushEdges cost edges queue).contains (cost + weight, next) = True
  | Nil, queue, next, weight, member => Void.exfalso member
  | Cons (first, firstWeight) rest, queue, next, weight, Inl here =>
    rewrite <- Eq.cong Pair.fst here, <- Eq.cong Pair.snd here in
      Graph.containsPushedKeeps cost rest (queue.insert (cost + firstWeight, first)) (cost + firstWeight, first)
        (Set.containsInsert (cost + firstWeight, first) queue)
  | Cons (first, firstWeight) rest, queue, next, weight, Inr later =>
    Graph.containsPushedEdge cost rest (queue.insert (cost + firstWeight, first)) next weight later

-- ...and nothing else.
theorem Graph.containsPushed [auto ord: Ord s] (cost: Nat): (edges: List (s, Nat)) → (queue: Set (Nat, s)) → (total: Nat) → (state: s) →
    (Graph.pushEdges cost edges queue).contains (total, state) = True →
    Or (queue.contains (total, state) = True) (Exists Nat (weight => And ((state, weight) ∈ edges) (total = cost + weight)))
  | Nil, queue, total, state, there => Inl there
  | Cons (next, weight) rest, queue, total, state, there =>
    match Graph.containsPushed cost rest (queue.insert (cost + weight, next)) total state there with
      | Inr (Witness found (Both member costs)) => Inr (Witness found (Both (Inr member) costs))
      | Inl inserted =>
        match same: (total, state) == (cost + weight, next) with
          | True =>
            let equal := DecEq.sound _ _ same
            Inr (Witness weight (Both (Inl (Eq.cong (found => (found, weight)) (Eq.sym (Eq.cong Pair.snd equal)))) (Eq.cong Pair.fst equal)))
          | False =>
            Inl (Eq.trans (Eq.sym (Set.containsInsertOther queue (cost + weight, next) (total, state) (DecEq.soundFalse _ _ same))) inserted)

-- `Less` then anything is never a first comparison of `Greater`.
theorem Graph.notGreaterOfThen: (first: Ordering) → (second: Ordering) → Ordering.andThen first second = Less → Not (first = Greater)
  | Less, second, less, same => Ordering.lessNotGreater same
  | Equal, second, less, same => Ordering.equalNotGreater same
  | Greater, second, less, same => Ordering.greaterNotLess less

-- The least pair of a queue costs no more than any pair in it.
theorem Graph.minLeast [auto ord: Ord s] (queue: Set (Nat, s)) (cost: Nat) (state: s) (found: queue.min = Some (cost, state)) (other: Nat)
    (otherState: s) (there: queue.contains (other, otherState) = True): cost ≤ other :=
  match entries: Map.toList queue.items with
    | Nil => Void.exfalso (Option.someNotNone (cost, state) (Eq.trans (Eq.sym found) (rewrite Map.minToList queue.items, entries in rfl)))
    | Cons (key, unit) rest =>
      let first: queue.min = Some key := rewrite Map.minToList queue.items, entries in rfl
      let same: key = (cost, state) := Option.someInjective _ _ (Eq.trans (Eq.sym first) found)
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

-- What the search may settle: the sources' states and the listed ones.
def Graph.universe (graph: Graph s) (sources: List (s, Nat)): List s := sources.map Pair.fst ++ graph.states

-- Every state queued is in the universe: at the start...
theorem Graph.startQueued [auto ord: Ord s] (graph: Graph s) (sources: List (s, Nat)) (cost: Nat) (state: s)
    (there: (Graph.pushEdges 0 sources Set.empty).contains (cost, state) = True): state ∈ graph.universe sources :=
  match Graph.containsPushed 0 sources Set.empty cost state there with
    | Inl none => Void.exfalso (Bool.falseNotTrue none)
    | Inr (Witness start (Both member costs)) =>
      List.memAppendLeft state (sources.map Pair.fst) graph.states (List.memMap sources (state, start) member Pair.fst)

-- ...after popping the least pair...
theorem Graph.restQueued [auto ord: Ord s] (graph: Graph s) (sources: List (s, Nat)) (queue: Set (Nat, s)) (popped: (Nat, s))
    (rest: Set (Nat, s)) (found: queue.popMin = Some (popped, rest))
    (queued: (cost: Nat) → (state: s) → queue.contains (cost, state) = True → state ∈ graph.universe sources) (cost: Nat) (state: s)
    (there: rest.contains (cost, state) = True): state ∈ graph.universe sources :=
  let (Both least restIs) := Set.popMinSome queue popped rest found
  queued cost state (Set.containsOfRemove queue popped (cost, state) (rewrite restIs at there in there))

-- ...and after pushing a state's edges.
theorem Graph.pushedQueued [auto ord: Ord s] (graph: Graph s) (sources: List (s, Nat)) (from: s) (fromCost: Nat) (rest: Set (Nat, s))
    (queued: (cost: Nat) → (state: s) → rest.contains (cost, state) = True → state ∈ graph.universe sources) (cost: Nat) (state: s)
    (there: (Graph.pushEdges fromCost (graph.edges from) rest).contains (cost, state) = True): state ∈ graph.universe sources :=
  match Graph.containsPushed fromCost (graph.edges from) rest cost state there with
    | Inl inRest => queued cost state inRest
    | Inr (Witness weight (Both edge costs)) =>
      List.memAppendRight state (sources.map Pair.fst) graph.states (graph.listed from state weight edge)

-- Dijkstra's algorithm: `queue` holds (cost, state) pairs still to look at,
-- least first; `settled` the least cost found for each state settled so
-- far. The least pair, `popped` with the rest of the queue, settles its
-- state, unless it already is, and queues the state's edges.
def Graph.searchFrom [auto ord: Ord s] (graph: Graph s) (sources: List (s, Nat)) (queue: Set (Nat, s)) (settled: Map s Nat)
    (queued: (cost: Nat) → (state: s) → queue.contains (cost, state) = True → state ∈ graph.universe sources):
    (popped: Option ((Nat, s), Set (Nat, s))) → queue.popMin = popped → Map s Nat
    decreasing (Graph.unsettledIn (graph.universe sources) settled, queue.size)
  | None, found => settled
  | Some ((cost, state), rest), found =>
    let restQueued := Graph.restQueued graph sources queue (cost, state) rest found queued
    if fresh: settled.contains state = False then
      let pushed := Graph.pushEdges cost (graph.edges state) rest
      Graph.searchFrom graph sources pushed (settled.insert state cost) (Graph.pushedQueued graph sources state cost rest restQueued) pushed.popMin rfl
        [decreasing :=
          Nat.LexLess.First
            (Graph.unsettledFewer (graph.universe sources) settled (settled.insert state cost)
              (other there => Map.containsInsertKeeps settled state cost other there) state
              (queued cost state (Set.containsMin queue (cost, state) (And.left (Set.popMinSome queue (cost, state) rest found)))) fresh
              (Map.containsInsertSame settled state cost))]
    else Graph.searchFrom graph sources rest settled restQueued rest.popMin rfl [decreasing := Nat.LexLess.Second rfl (Set.sizePopMin queue (cost, state) rest found)]

-- The least cost to each state reachable from one of the sources, each
-- given with the cost of starting there.
def Graph.distances [auto ord: Ord s] (graph: Graph s) (sources: List (s, Nat)): Map s Nat :=
  let queue := Graph.pushEdges 0 sources Set.empty
  graph.searchFrom sources queue Map.empty (Graph.startQueued graph sources) queue.popMin rfl

-- One step of the search: an empty queue ends it...
theorem Graph.searchEmpty [auto ord: Ord s] (graph: Graph s) (sources: List (s, Nat)) (queue: Set (Nat, s)) (settled: Map s Nat)
    (queued: (cost: Nat) → (state: s) → queue.contains (cost, state) = True → state ∈ graph.universe sources) (found: queue.popMin = None):
    graph.searchFrom sources queue settled queued None found = settled :=
  rewrite Graph.searchFrom.unfold graph sources queue settled queued None found in rfl

-- ...a state already settled is dropped...
theorem Graph.searchSkip [auto ord: Ord s] (graph: Graph s) (sources: List (s, Nat)) (queue: Set (Nat, s)) (settled: Map s Nat)
    (queued: (cost: Nat) → (state: s) → queue.contains (cost, state) = True → state ∈ graph.universe sources) (cost: Nat) (state: s)
    (rest: Set (Nat, s)) (found: queue.popMin = Some ((cost, state), rest)) (taken: settled.contains state = True):
    graph.searchFrom sources queue settled queued (Some ((cost, state), rest)) found
      = graph.searchFrom sources rest settled (Graph.restQueued graph sources queue (cost, state) rest found queued) rest.popMin rfl :=
  rewrite Graph.searchFrom.unfold graph sources queue settled queued (Some ((cost, state), rest)) found in
    Decidable.elimEq _ _ _ _ (fresh => Void.exfalso (Bool.falseNotTrue (Eq.trans (Eq.sym fresh) taken))) (other => rfl)

-- ...and one not settled yet is settled, with its edges queued.
theorem Graph.searchSettle [auto ord: Ord s] (graph: Graph s) (sources: List (s, Nat)) (queue: Set (Nat, s)) (settled: Map s Nat)
    (queued: (cost: Nat) → (state: s) → queue.contains (cost, state) = True → state ∈ graph.universe sources) (cost: Nat) (state: s)
    (rest: Set (Nat, s)) (found: queue.popMin = Some ((cost, state), rest)) (fresh: settled.contains state = False):
    graph.searchFrom sources queue settled queued (Some ((cost, state), rest)) found
      = graph.searchFrom sources (Graph.pushEdges cost (graph.edges state) rest) (settled.insert state cost)
        (Graph.pushedQueued graph sources state cost rest (Graph.restQueued graph sources queue (cost, state) rest found queued))
        (Graph.pushEdges cost (graph.edges state) rest).popMin rfl :=
  rewrite Graph.searchFrom.unfold graph sources queue settled queued (Some ((cost, state), rest)) found in
    Decidable.elimEq _ _ _ _ (isFresh => rfl) (notFresh => Void.exfalso (notFresh fresh))

-- A cost the search still has to account for: the pair is queued, or the
-- state is settled for no more.
def Graph.Pending [auto ord: Ord s] (queue: Set (Nat, s)) (settled: Map s Nat) (cost: Nat) (state: s): Prop :=
  Or (queue.contains (cost, state) = True) (Graph.Bound settled cost state)

-- What holds at each step of the search: every queued pair and settled
-- state is reached for its cost; each source, and each edge out of a
-- settled state, is pending; and nothing settled costs more than anything
-- queued.
def Graph.SearchState [auto ord: Ord s] (graph: Graph s) (sources: List (s, Nat)) (reach: s → Nat → Prop) (queue: Set (Nat, s))
    (settled: Map s Nat): Prop :=
  And ((cost: Nat) → (state: s) → queue.contains (cost, state) = True → reach state cost)
    (And ((state: s) → (cost: Nat) → settled.get state = Some cost → reach state cost)
      (And ((source: s) → (start: Nat) → (source, start) ∈ sources → Graph.Pending queue settled start source)
        (And
          ((state: s) → (cost: Nat) → settled.get state = Some cost → (next: s) → (weight: Nat) → (next, weight) ∈ graph.edges state →
            Graph.Pending queue settled (cost + weight) next)
          ((state: s) → (cost: Nat) → settled.get state = Some cost → (other: Nat) → (otherState: s) →
            queue.contains (other, otherState) = True → cost ≤ other))))

-- A pending cost stays pending when the queue keeps all but the popped
-- pair, the settled states stay, and the popped state is settled for no
-- more than the popped cost.
theorem Graph.pendingKept [auto ord: Ord s] (queue: Set (Nat, s)) (newQueue: Set (Nat, s)) (settled: Map s Nat) (newSettled: Map s Nat)
    (poppedCost: Nat) (poppedState: s) (poppedFound: Nat)
    (kept: (entry: (Nat, s)) → queue.contains entry = True → Not (entry = (poppedCost, poppedState)) → newQueue.contains entry = True)
    (stays: (state: s) → (found: Nat) → settled.get state = Some found → newSettled.get state = Some found)
    (popped: newSettled.get poppedState = Some poppedFound) (cheaper: poppedFound ≤ poppedCost) (cost: Nat) (state: s)
    (pending: Graph.Pending queue settled cost state): Graph.Pending newQueue newSettled cost state :=
  match pending with
    | Inr (Witness found (Both got le)) => Inr (Witness found (Both (stays state found got) le))
    | Inl there =>
      match same: (cost, state) == (poppedCost, poppedState) with
        | True =>
          let equal := DecEq.sound _ _ same
          Inr (Witness poppedFound (Both (rewrite Eq.cong Pair.snd equal in popped) (rewrite Eq.cong Pair.fst equal in cheaper)))
        | False => Inl (kept (cost, state) there (DecEq.soundFalse _ _ same))

-- With nothing queued, a pending cost is a bound.
theorem Graph.boundOfPending [auto ord: Ord s] (queue: Set (Nat, s)) (settled: Map s Nat) (empty: queue.popMin = None) (cost: Nat) (state: s)
    (pending: Graph.Pending queue settled cost state): Graph.Bound settled cost state :=
  match pending with
    | Inr bound => bound
    | Inl there =>
      Void.exfalso (Bool.falseNotTrue (Eq.trans (Eq.sym (Set.missingOfMinNone queue (Set.popMinNone queue empty) (cost, state))) there))

-- Dropping a popped pair whose state is settled keeps the search state.
theorem Graph.skipKeeps [auto ord: Ord s] (graph: Graph s) (sources: List (s, Nat)) (reach: s → Nat → Prop) (queue: Set (Nat, s))
    (settled: Map s Nat) (cost: Nat) (state: s) (found: queue.min = Some (cost, state)) (taken: settled.contains state = True)
    (invariant: Graph.SearchState graph sources reach queue settled): Graph.SearchState graph sources reach (queue.remove (cost, state)) settled :=
  let (Both queuedReach (Both settledReached (Both sourcesPending (Both edgesPending ordered)))) := invariant
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
            (from fromCost got other otherState there =>
              ordered from fromCost got other otherState (Set.containsOfRemove queue (cost, state) (other, otherState) there))))))

-- Settling the popped state and queueing its edges keeps the search state.
theorem Graph.settleKeeps [auto ord: Ord s] (graph: Graph s) (sources: List (s, Nat)) (reach: s → Nat → Prop)
    (edgesReach: (state: s) → (cost: Nat) → reach state cost → (next: s) → (weight: Nat) → (next, weight) ∈ graph.edges state →
      reach next (cost + weight))
    (queue: Set (Nat, s)) (settled: Map s Nat) (cost: Nat) (state: s) (found: queue.min = Some (cost, state))
    (fresh: settled.contains state = False) (invariant: Graph.SearchState graph sources reach queue settled):
    Graph.SearchState graph sources reach (Graph.pushEdges cost (graph.edges state) (queue.remove (cost, state))) (settled.insert state cost) :=
  let (Both queuedReach (Both settledReached (Both sourcesPending (Both edgesPending ordered)))) := invariant
  let rest := queue.remove (cost, state)
  let pushed := Graph.pushEdges cost (graph.edges state) rest
  let inQueue := Set.containsMin queue (cost, state) found
  let reached := queuedReach cost state inQueue
  let poppedGot: (settled.insert state cost).get state = Some cost := Map.getInsert state cost settled
  let keep := Graph.pendingKept queue pushed settled (settled.insert state cost) cost state cost
    (entry there apart =>
      Graph.containsPushedKeeps cost (graph.edges state) rest entry (Eq.trans (Set.containsRemoveOther queue (cost, state) entry apart) there))
    (other value got => Map.getInsertKeeps settled state cost fresh other value got) poppedGot (Nat.leRefl cost)
  let atLeast: (other: Nat) → (otherState: s) → pushed.contains (other, otherState) = True → cost ≤ other :=
    other otherState there =>
      match Graph.containsPushed cost (graph.edges state) rest other otherState there with
        | Inl inRest => Graph.minLeast queue cost state found other otherState (Set.containsOfRemove queue (cost, state) (other, otherState) inRest)
        | Inr (Witness weight (Both edge costs)) => rewrite costs in omega
  Both
    (other otherState there =>
      match Graph.containsPushed cost (graph.edges state) rest other otherState there with
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
                rewrite costs in Inl (Graph.containsPushedEdge cost (graph.edges state) rest next weight (rewrite <- same in edge))
              | Inr old => keep (fromCost + weight) next (edgesPending from fromCost old next weight edge))
          (from fromCost got other otherState there =>
            match Map.getInsertCases settled state cost from fromCost got with
              | Inl (Both same costs) => rewrite costs in atLeast other otherState there
              | Inr old => omega [ordered from fromCost old cost state inQueue, atLeast other otherState there]))))

-- The search returns what `SearchResult` says, from any search state.
theorem Graph.searchFromCorrect [auto ord: Ord s] (graph: Graph s) (sources: List (s, Nat)) (reach: s → Nat → Prop)
    (edgesReach: (state: s) → (cost: Nat) → reach state cost → (next: s) → (weight: Nat) → (next, weight) ∈ graph.edges state →
      reach next (cost + weight))
    (queue: Set (Nat, s)) (settled: Map s Nat)
    (queued: (cost: Nat) → (state: s) → queue.contains (cost, state) = True → state ∈ graph.universe sources):
    (popped: Option ((Nat, s), Set (Nat, s))) → (found: queue.popMin = popped) → Graph.SearchState graph sources reach queue settled →
      Graph.SearchResult graph sources reach (graph.searchFrom sources queue settled queued popped found)
    decreasing (Graph.unsettledIn (graph.universe sources) settled, queue.size)
  | None, found, invariant =>
    rewrite Graph.searchEmpty graph sources queue settled queued found in
      let (Both queuedReach (Both settledReached (Both sourcesPending (Both edgesPending ordered)))) := invariant
      Both settledReached
        (Both (source start member => Graph.boundOfPending queue settled found start source (sourcesPending source start member))
          (from fromCost got next weight edge =>
            Graph.boundOfPending queue settled found (fromCost + weight) next (edgesPending from fromCost got next weight edge)))
  | Some ((cost, state), rest), found, invariant =>
    let (Both least restIs) := Set.popMinSome queue (cost, state) rest found
    let restQueued := Graph.restQueued graph sources queue (cost, state) rest found queued
    match taken: settled.contains state with
      | True =>
        rewrite Graph.searchSkip graph sources queue settled queued cost state rest found taken in
          Graph.searchFromCorrect graph sources reach edgesReach rest settled restQueued rest.popMin rfl
            (rewrite restIs in Graph.skipKeeps graph sources reach queue settled cost state least taken invariant)
            [decreasing := Nat.LexLess.Second rfl (Set.sizePopMin queue (cost, state) rest found)]
      | False =>
        rewrite Graph.searchSettle graph sources queue settled queued cost state rest found taken in
          Graph.searchFromCorrect graph sources reach edgesReach (Graph.pushEdges cost (graph.edges state) rest) (settled.insert state cost)
            (Graph.pushedQueued graph sources state cost rest restQueued) (Graph.pushEdges cost (graph.edges state) rest).popMin rfl
            (rewrite restIs in Graph.settleKeeps graph sources reach edgesReach queue settled cost state least taken invariant)
            [decreasing :=
              Nat.LexLess.First
                (Graph.unsettledFewer (graph.universe sources) settled (settled.insert state cost)
                  (other there => Map.containsInsertKeeps settled state cost other there) state
                  (queued cost state (Set.containsMin queue (cost, state) least)) taken (Map.containsInsertSame settled state cost))]

-- Dijkstra's search returns what `SearchResult` says, for any `reach` that
-- holds at each source for its starting cost and along each edge.
theorem Graph.distancesCorrect [auto ord: Ord s] (graph: Graph s) (sources: List (s, Nat)) (reach: s → Nat → Prop)
    (sourcesReach: (source: s) → (start: Nat) → (source, start) ∈ sources → reach source start)
    (edgesReach: (state: s) → (cost: Nat) → reach state cost → (next: s) → (weight: Nat) → (next, weight) ∈ graph.edges state →
      reach next (cost + weight)):
    Graph.SearchResult graph sources reach (graph.distances sources) :=
  let queue := Graph.pushEdges 0 sources Set.empty
  let initial: Graph.SearchState graph sources reach queue Map.empty :=
    Both
      (cost state there =>
        match Graph.containsPushed 0 sources Set.empty cost state there with
          | Inl none => Void.exfalso (Bool.falseNotTrue none)
          | Inr (Witness start (Both member costs)) =>
            let same: cost = start := omega
            rewrite same in sourcesReach state start member)
      (Both (state cost got => Void.exfalso (Option.noneNotSome cost got))
        (Both
          (source start member =>
            let same: 0 + start = start := omega
            Inl (rewrite <- same in Graph.containsPushedEdge 0 sources Set.empty source start member))
          (Both (state cost got => Void.exfalso (Option.noneNotSome cost got)) (state cost got => Void.exfalso (Option.noneNotSome cost got)))))
  Graph.searchFromCorrect graph sources reach edgesReach queue Map.empty (Graph.startQueued graph sources) queue.popMin rfl initial

-- Each cost Dijkstra's search finds is a walk's from a source, and no walk
-- from a source costs less.
theorem Graph.distancesShortest [auto ord: Ord s] (graph: Graph s) (sources: List (s, Nat)): Graph.Shortest graph sources (graph.distances sources) :=
  Graph.shortestOfResult graph sources (graph.distances sources)
    (Graph.distancesCorrect graph sources (graph.Reached sources) (Graph.reachedSources graph sources) (Graph.reachedEdges graph sources))

-- Breadth-first search

-- Each edge's state not settled yet: settled at `depth`, and put on
-- `next`.
def Graph.visitEdges [auto ord: Ord s] (depth: Nat): (edges: List (s, Nat)) → (settled: Map s Nat) → (next: List s) → (Map s Nat, List s)
  | Nil, settled, next => (settled, next)
  | Cons (state, weight) rest, settled, next =>
    if settled.contains state then Graph.visitEdges depth rest settled next
    else Graph.visitEdges depth rest (settled.insert state depth) (Cons state next)

-- What visiting edges settled stays settled...
theorem Graph.visitGrows [auto ord: Ord s] (depth: Nat): (edges: List (s, Nat)) → (settled: Map s Nat) → (next: List s) → (state: s) →
    (cost: Nat) → settled.get state = Some cost → (Graph.visitEdges depth edges settled next).fst.get state = Some cost
  | Nil, settled, next, state, cost, got => got
  | Cons (target, weight) rest, settled, next, state, cost, got =>
    match there: settled.contains target with
      | True => Graph.visitGrows depth rest settled next state cost got
      | False =>
        Graph.visitGrows depth rest (settled.insert target depth) (Cons target next) state cost
          (Map.getInsertKeeps settled target depth there state cost got)

-- ...what was on the list stays on it...
theorem Graph.visitListed [auto ord: Ord s] (depth: Nat): (edges: List (s, Nat)) → (settled: Map s Nat) → (next: List s) → (state: s) →
    state ∈ next → state ∈ (Graph.visitEdges depth edges settled next).snd
  | Nil, settled, next, state, member => member
  | Cons (target, weight) rest, settled, next, state, member =>
    match there: settled.contains target with
      | True => Graph.visitListed depth rest settled next state member
      | False => Graph.visitListed depth rest (settled.insert target depth) (Cons target next) state (Inr member)

-- ...what it settles anew is at `depth`, and put on the list...
theorem Graph.visitNew [auto ord: Ord s] (depth: Nat): (edges: List (s, Nat)) → (settled: Map s Nat) → (next: List s) → (state: s) →
    (cost: Nat) → (Graph.visitEdges depth edges settled next).fst.get state = Some cost →
    Or (settled.get state = Some cost)
      (And (cost = depth) (And (state ∈ (Graph.visitEdges depth edges settled next).snd) (Exists Nat (weight => (state, weight) ∈ edges))))
  | Nil, settled, next, state, cost, got => Inl got
  | Cons (target, weight) rest, settled, next, state, cost, got =>
    match there: settled.contains target with
      | True =>
        match Graph.visitNew depth rest settled next state cost got with
          | Inl old => Inl old
          | Inr (Both costs (Both listed (Witness found edge))) => Inr (Both costs (Both listed (Witness found (Inr edge))))
      | False =>
        match Graph.visitNew depth rest (settled.insert target depth) (Cons target next) state cost got with
          | Inr (Both costs (Both listed (Witness found edge))) => Inr (Both costs (Both listed (Witness found (Inr edge))))
          | Inl inserted =>
            match Map.getInsertCases settled target depth state cost inserted with
              | Inr old => Inl old
              | Inl (Both same costs) =>
                Inr
                  (Both costs
                    (Both (Graph.visitListed depth rest (settled.insert target depth) (Cons target next) state (Inl (Eq.sym same)))
                      (Witness weight (Inl (rewrite same in rfl)))))

-- ...what is on it was on it, or wasn't settled before and is now, at
-- `depth`, an edge's state...
theorem Graph.visitAdded [auto ord: Ord s] (depth: Nat): (edges: List (s, Nat)) → (settled: Map s Nat) → (next: List s) → (state: s) →
    state ∈ (Graph.visitEdges depth edges settled next).snd →
    Or (state ∈ next)
      (And (settled.contains state = False)
        (And ((Graph.visitEdges depth edges settled next).fst.get state = Some depth) (Exists Nat (weight => (state, weight) ∈ edges))))
  | Nil, settled, next, state, member => Inl member
  | Cons (target, weight) rest, settled, next, state, member =>
    match there: settled.contains target with
      | True =>
        match Graph.visitAdded depth rest settled next state member with
          | Inl old => Inl old
          | Inr (Both fresh (Both got (Witness found edge))) => Inr (Both fresh (Both got (Witness found (Inr edge))))
      | False =>
        match Graph.visitAdded depth rest (settled.insert target depth) (Cons target next) state member with
          | Inl (Inl same) =>
            rewrite <- same in
              Inr
                (Both there
                  (Both
                    (Graph.visitGrows depth rest (settled.insert target depth) (Cons target next) target depth
                      (Map.getInsert target depth settled))
                    (Witness weight (Inl rfl))))
          | Inl (Inr old) => Inl old
          | Inr (Both fresh (Both got (Witness found edge))) =>
            let before: settled.contains state = False :=
              match was: settled.contains state with
                | False => rfl
                | True => Void.exfalso (Bool.falseNotTrue (Eq.trans (Eq.sym fresh) (Map.containsInsertKeeps settled target depth state was)))
            Inr (Both before (Both got (Witness found (Inr edge))))

-- ...and every edge's state is settled.
theorem Graph.visitCovers [auto ord: Ord s] (depth: Nat): (edges: List (s, Nat)) → (settled: Map s Nat) → (next: List s) → (state: s) →
    (weight: Nat) → (state, weight) ∈ edges → (Graph.visitEdges depth edges settled next).fst.contains state = True
  | Nil, settled, next, state, weight, member => Void.exfalso member
  | Cons (target, targetWeight) rest, settled, next, state, weight, member =>
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
            settles (settled.insert target depth) (Cons target next)
              (rewrite <- Eq.cong Pair.fst here in Map.containsInsertSame settled target depth)
          | Inr later => Graph.visitCovers depth rest (settled.insert target depth) (Cons target next) state weight later

-- One level of the search: the edges out of the frontier, visited.
def Graph.visitFrontier [auto ord: Ord s] (graph: Graph s) (depth: Nat) (frontier: List s) (settled: Map s Nat): (Map s Nat, List s) :=
  Graph.visitEdges depth (frontier.flatMap graph.edges) settled Nil

-- A frontier visited with states added leaves fewer unsettled.
theorem Graph.visitFewer [auto ord: Ord s] (graph: Graph s) (depth: Nat) (frontier: List s) (settled: Map s Nat) (more: Map s Nat)
    (first: s) (rest: List s) (found: graph.visitFrontier depth frontier settled = (more, Cons first rest)):
    Graph.unsettledIn graph.states more < Graph.unsettledIn graph.states settled :=
  let edges := frontier.flatMap graph.edges
  let listedFirst: first ∈ (Graph.visitEdges depth edges settled Nil).snd := rewrite found in Inl rfl
  let moreIs: (Graph.visitEdges depth edges settled Nil).fst = more := Eq.cong Pair.fst found
  match Graph.visitAdded depth edges settled Nil first listedFirst with
    | Inl none => Void.exfalso none
    | Inr (Both fresh (Both got (Witness weight edge))) =>
      List.anyElim (from => (first, weight) ∈ graph.edges from) (Graph.unsettledIn graph.states more < Graph.unsettledIn graph.states settled)
        frontier (List.memFlatMapElim graph.edges (first, weight) frontier edge) (from inFrontier fromEdge =>
          Graph.unsettledFewer graph.states settled more
            (state there =>
              Exists.elim (Map.getOfContains settled state there) (cost old =>
                Map.containsOfGet more state cost (rewrite <- moreIs in Graph.visitGrows depth edges settled Nil state cost old)))
            first (graph.listed from first weight fromEdge) fresh (Map.containsOfGet more first depth (rewrite <- moreIs in got)))

-- Breadth-first search: `frontier` holds the states settled at `depth`.
-- The states their edges lead to that aren't settled yet are settled at
-- `depth + 1`, `visited` with the next frontier.
def Graph.breadthFrom [auto ord: Ord s] (graph: Graph s) (depth: Nat) (settled: Map s Nat) (frontier: List s):
    (visited: (Map s Nat, List s)) → graph.visitFrontier (depth + 1) frontier settled = visited → Map s Nat
    decreasing Graph.unsettledIn graph.states settled
  | (more, Nil), found => more
  | (more, Cons first rest), found =>
    graph.breadthFrom (depth + 1) more (Cons first rest) (graph.visitFrontier (depth + 1 + 1) (Cons first rest) more) rfl
      [decreasing := Graph.visitFewer graph (depth + 1) frontier settled more first rest found]

-- The fewest edges from any of the sources to each state reachable from
-- them, each edge counting 1 whatever its cost.
def Graph.breadthFirst [auto ord: Ord s] (graph: Graph s) (sources: List s): Map s Nat :=
  let start := Graph.visitEdges 0 (sources.map (source => (source, 0))) Map.empty Nil
  graph.breadthFrom 0 start.fst start.snd (graph.visitFrontier (0 + 1) start.snd start.fst) rfl

theorem Graph.breadthDone [auto ord: Ord s] (graph: Graph s) (depth: Nat) (settled: Map s Nat) (frontier: List s) (more: Map s Nat)
    (found: graph.visitFrontier (depth + 1) frontier settled = (more, Nil)): graph.breadthFrom depth settled frontier (more, Nil) found = more :=
  rewrite Graph.breadthFrom.unfold graph depth settled frontier (more, Nil) found in rfl

theorem Graph.breadthStep [auto ord: Ord s] (graph: Graph s) (depth: Nat) (settled: Map s Nat) (frontier: List s) (more: Map s Nat) (first: s)
    (rest: List s) (found: graph.visitFrontier (depth + 1) frontier settled = (more, Cons first rest)):
    graph.breadthFrom depth settled frontier (more, Cons first rest) found
      = graph.breadthFrom (depth + 1) more (Cons first rest) (graph.visitFrontier (depth + 1 + 1) (Cons first rest) more) rfl :=
  rewrite Graph.breadthFrom.unfold graph depth settled frontier (more, Cons first rest) found in rfl

-- What holds at each level of the search, for a `reach` that holds at the
-- sources for 0 and along every edge for one more: every settled state is
-- reached for its cost, at most `depth`; the frontier is exactly the
-- states settled at `depth`; each edge out of a state settled below it
-- leads to one settled for one more at most; and each source is settled
-- at 0.
def Graph.BreadthState [auto ord: Ord s] (graph: Graph s) (sources: List s) (reach: s → Nat → Prop) (depth: Nat) (settled: Map s Nat)
    (frontier: List s): Prop :=
  And ((state: s) → (cost: Nat) → settled.get state = Some cost → And (reach state cost) (cost ≤ depth))
    (And ((state: s) → Iff (state ∈ frontier) (settled.get state = Some depth))
      (And
        ((state: s) → (cost: Nat) → settled.get state = Some cost → cost < depth → (next: s) → (weight: Nat) →
          (next, weight) ∈ graph.edges state → Graph.Bound settled (cost + 1) next)
        ((source: s) → source ∈ sources → Graph.Bound settled 0 source)))

-- A bound survives visiting.
theorem Graph.visitBound [auto ord: Ord s] (depth: Nat) (edges: List (s, Nat)) (settled: Map s Nat) (next: List s) (cost: Nat) (state: s)
    (bound: Graph.Bound settled cost state): Graph.Bound (Graph.visitEdges depth edges settled next).fst cost state :=
  Exists.elim bound (found both => Witness found (Both (Graph.visitGrows depth edges settled next state found (And.left both)) (And.right both)))

-- Each edge out of the frontier leads to a state settled for one more at
-- most, after visiting it.
theorem Graph.frontierClosed [auto ord: Ord s] (graph: Graph s) (sources: List s) (reach: s → Nat → Prop) (depth: Nat) (settled: Map s Nat)
    (frontier: List s) (invariant: Graph.BreadthState graph sources reach depth settled frontier) (state: s) (inFrontier: state ∈ frontier)
    (next: s) (weight: Nat) (edge: (next, weight) ∈ graph.edges state):
    Graph.Bound (graph.visitFrontier (depth + 1) frontier settled).fst (depth + 1) next :=
  let (Both settledReach rest) := invariant
  let edges := frontier.flatMap graph.edges
  let covered := Graph.visitCovers (depth + 1) edges settled Nil next weight (List.memFlatMapIntro graph.edges state (next, weight) frontier inFrontier edge)
  Exists.elim (Map.getOfContains _ next covered) (cost got =>
    match Graph.visitNew (depth + 1) edges settled Nil next cost got with
      | Inl old => Witness cost (Both got (omega [And.right (settledReach next cost old)]))
      | Inr (Both costs others) => Witness cost (Both got (omega [costs])))

-- With no next frontier, the search state is the search result.
theorem Graph.breadthDoneCorrect [auto ord: Ord s] (graph: Graph s) (sources: List s) (reach: s → Nat → Prop) (depth: Nat) (settled: Map s Nat)
    (frontier: List s) (more: Map s Nat) (found: graph.visitFrontier (depth + 1) frontier settled = (more, Nil))
    (invariant: Graph.BreadthState graph sources reach depth settled frontier)
    (unit: (state: s) → (next: s) → (weight: Nat) → (next, weight) ∈ graph.edges state → weight = 1):
    Graph.SearchResult graph (sources.map (source => (source, 0))) reach more :=
  let (Both settledReach (Both atFrontier (Both closedBelow sourcesBound))) := invariant
  let edges := frontier.flatMap graph.edges
  let moreIs: (Graph.visitEdges (depth + 1) edges settled Nil).fst = more := Eq.cong Pair.fst found
  let nextIs: (Graph.visitEdges (depth + 1) edges settled Nil).snd = Nil := Eq.cong Pair.snd found
  let old: (state: s) → (cost: Nat) → more.get state = Some cost → settled.get state = Some cost :=
    state cost got =>
      match Graph.visitNew (depth + 1) edges settled Nil state cost (rewrite moreIs in got) with
        | Inl was => was
        | Inr (Both costs (Both listed others)) => Void.exfalso (rewrite nextIs at listed in listed)
  let grows: (cost: Nat) → (state: s) → Graph.Bound settled cost state → Graph.Bound more cost state :=
    cost state bound => rewrite <- moreIs in Graph.visitBound (depth + 1) edges settled Nil cost state bound
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

-- One level keeps the search state.
theorem Graph.breadthKeeps [auto ord: Ord s] (graph: Graph s) (sources: List s) (reach: s → Nat → Prop)
    (edgesReach: (state: s) → (cost: Nat) → reach state cost → (next: s) → (weight: Nat) → (next, weight) ∈ graph.edges state →
      reach next (cost + weight))
    (unit: (state: s) → (next: s) → (weight: Nat) → (next, weight) ∈ graph.edges state → weight = 1) (depth: Nat) (settled: Map s Nat)
    (frontier: List s) (more: Map s Nat) (nextFrontier: List s) (found: graph.visitFrontier (depth + 1) frontier settled = (more, nextFrontier))
    (invariant: Graph.BreadthState graph sources reach depth settled frontier): Graph.BreadthState graph sources reach (depth + 1) more nextFrontier :=
  let (Both settledReach (Both atFrontier (Both closedBelow sourcesBound))) := invariant
  let edges := frontier.flatMap graph.edges
  let moreIs: (Graph.visitEdges (depth + 1) edges settled Nil).fst = more := Eq.cong Pair.fst found
  let nextIs: (Graph.visitEdges (depth + 1) edges settled Nil).snd = nextFrontier := Eq.cong Pair.snd found
  let grows: (cost: Nat) → (state: s) → Graph.Bound settled cost state → Graph.Bound more cost state :=
    cost state bound => rewrite <- moreIs in Graph.visitBound (depth + 1) edges settled Nil cost state bound
  -- What is settled now was settled before, or is new at `depth + 1` and
  -- on the next frontier.
  let origin: (state: s) → (cost: Nat) → more.get state = Some cost →
      Or (settled.get state = Some cost) (And (cost = depth + 1) (And (state ∈ nextFrontier) (Exists Nat (weight => (state, weight) ∈ edges)))) :=
    state cost got => rewrite <- nextIs in Graph.visitNew (depth + 1) edges settled Nil state cost (rewrite moreIs in got)
  Both
    (state cost got =>
      match origin state cost got with
        | Inl old =>
          let (Both reached below) := settledReach state cost old
          Both reached (omega [below])
        | Inr (Both costs (Both listed (Witness weight edge))) =>
          List.anyElim (from => (state, weight) ∈ graph.edges from) (And (reach state cost) (cost ≤ depth + 1)) frontier
            (List.memFlatMapElim graph.edges (state, weight) frontier edge) (from inFrontier fromEdge =>
              let fromGot := (atFrontier from).forward inFrontier
              let reached := edgesReach from depth (And.left (settledReach from depth fromGot)) state weight fromEdge
              rewrite costs in Both (rewrite <- unit from state weight fromEdge in reached) (Nat.leRefl (depth + 1))))
    (Both
      (state => {
        forward = listed =>
          match Graph.visitAdded (depth + 1) edges settled Nil state (rewrite nextIs in listed) with
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

-- The search returns what `SearchResult` says, from any search state.
theorem Graph.breadthFromCorrect [auto ord: Ord s] (graph: Graph s) (sources: List s) (reach: s → Nat → Prop)
    (edgesReach: (state: s) → (cost: Nat) → reach state cost → (next: s) → (weight: Nat) → (next, weight) ∈ graph.edges state →
      reach next (cost + weight))
    (unit: (state: s) → (next: s) → (weight: Nat) → (next, weight) ∈ graph.edges state → weight = 1) (depth: Nat) (settled: Map s Nat)
    (frontier: List s):
    (visited: (Map s Nat, List s)) → (found: graph.visitFrontier (depth + 1) frontier settled = visited) →
      Graph.BreadthState graph sources reach depth settled frontier →
      Graph.SearchResult graph (sources.map (source => (source, 0))) reach (graph.breadthFrom depth settled frontier visited found)
    decreasing Graph.unsettledIn graph.states settled
  | (more, Nil), found, invariant =>
    rewrite Graph.breadthDone graph depth settled frontier more found in
      Graph.breadthDoneCorrect graph sources reach depth settled frontier more found invariant unit
  | (more, Cons first rest), found, invariant =>
    rewrite Graph.breadthStep graph depth settled frontier more first rest found in
      Graph.breadthFromCorrect graph sources reach edgesReach unit (depth + 1) more (Cons first rest)
        (graph.visitFrontier (depth + 1 + 1) (Cons first rest) more) rfl
        (Graph.breadthKeeps graph sources reach edgesReach unit depth settled frontier more (Cons first rest) found invariant)
        [decreasing := Graph.visitFewer graph (depth + 1) frontier settled more first rest found]

-- Breadth-first search returns what `SearchResult` says, for a graph whose
-- edges each cost 1 and any `reach` that holds at each source for 0 and
-- along each edge.
theorem Graph.breadthFirstCorrect [auto ord: Ord s] (graph: Graph s) (sources: List s) (reach: s → Nat → Prop)
    (sourcesReach: (source: s) → source ∈ sources → reach source 0)
    (edgesReach: (state: s) → (cost: Nat) → reach state cost → (next: s) → (weight: Nat) → (next, weight) ∈ graph.edges state →
      reach next (cost + weight))
    (unit: (state: s) → (next: s) → (weight: Nat) → (next, weight) ∈ graph.edges state → weight = 1):
    Graph.SearchResult graph (sources.map (source => (source, 0))) reach (graph.breadthFirst sources) :=
  let edges := sources.map (source => (source, 0))
  let start := Graph.visitEdges 0 edges Map.empty Nil
  let fromSource: (state: s) → (weight: Nat) → (state, weight) ∈ edges → state ∈ sources :=
    state weight member =>
      List.anyElim (source => (source, 0) = (state, weight)) (state ∈ sources) sources (List.memMapAny sources (source => (source, 0)) (state, weight) member)
        (source inSources same => rewrite <- Eq.cong Pair.fst same in inSources)
  let origin: (state: s) → (cost: Nat) → start.fst.get state = Some cost →
      And (cost = 0) (And (state ∈ start.snd) (state ∈ sources)) :=
    state cost got =>
      match Graph.visitNew 0 edges Map.empty Nil state cost got with
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
            match Graph.visitAdded 0 edges Map.empty Nil state listed with
              | Inl none => Void.exfalso none
              | Inr (Both fresh (Both got others)) => got,
          backward = got => And.left (And.right (origin state 0 got))
        })
        (Both (state cost got below => Void.exfalso (omega [below]))
          (source member =>
            let covered := Graph.visitCovers 0 edges Map.empty Nil source 0 (List.memMap sources source member (other => (other, 0)))
            Exists.elim (Map.getOfContains _ source covered) (cost got =>
              Witness cost (Both got (omega [And.left (origin source cost got)]))))))
  Graph.breadthFromCorrect graph sources reach edgesReach unit 0 start.fst start.snd (graph.visitFrontier (0 + 1) start.snd start.fst) rfl initial

-- On a graph whose edges each cost 1, each count breadth-first search finds
-- is a walk's from a source, and no walk from a source has fewer edges.
theorem Graph.breadthFirstShortest [auto ord: Ord s] (graph: Graph s) (sources: List s)
    (unit: (state: s) → (next: s) → (weight: Nat) → (next, weight) ∈ graph.edges state → weight = 1):
    Graph.Shortest graph (sources.map (source => (source, 0))) (graph.breadthFirst sources) :=
  let starts := sources.map (source => (source, 0))
  Graph.shortestOfResult graph starts (graph.breadthFirst sources)
    (Graph.breadthFirstCorrect graph sources (graph.Reached starts)
      (source member => Graph.reachedSources graph starts source 0 (List.memMap sources source member (other => (other, 0))))
      (Graph.reachedEdges graph starts) unit)
