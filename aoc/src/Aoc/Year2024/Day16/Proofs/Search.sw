-- Dijkstra's search, for any graph: what it settles is reached for that
-- cost (`searchSound`), and nothing reaches a state for less
-- (`searchClosed`, from which the maze's proofs follow any path).

namespace Aoc.Year2024.Day16.Proofs
import Aoc.Year2024.Day16 (..)
import Std (And, Bool, DecEq, Decidable, Eq, Exists, Iff, List, Map, Nat, Option, Or, Set, Void)

-- One step of the search: an empty queue ends it...
theorem searchEmpty [auto ord: Ord s] (graph: Graph s) (queue: Set (Nat, s)) (settled: Map s Nat) (found: queue.popMin = None):
    graph.searchFrom queue settled None found = settled :=
  rewrite Graph.searchFrom.unfold graph queue settled None found in rfl

-- ...a state already settled is dropped...
theorem searchSkip [auto ord: Ord s] (graph: Graph s) (queue: Set (Nat, s)) (settled: Map s Nat) (cost: Nat) (state: s) (rest: Set (Nat, s))
    (found: queue.popMin = Some ((cost, state), rest)) (taken: settled.contains state = True):
    graph.searchFrom queue settled (Some ((cost, state), rest)) found = graph.searchFrom rest settled rest.popMin rfl :=
  rewrite Graph.searchFrom.unfold graph queue settled (Some ((cost, state), rest)) found in
    Decidable.elimEq _ _ _ _ (fresh => Void.exfalso (Bool.falseNotTrue (Eq.trans (Eq.sym fresh) taken))) (other => rfl)

-- ...and one not settled yet is settled, with its neighbours queued.
theorem searchSettle [auto ord: Ord s] (graph: Graph s) (queue: Set (Nat, s)) (settled: Map s Nat) (cost: Nat) (state: s) (rest: Set (Nat, s))
    (found: queue.popMin = Some ((cost, state), rest)) (fresh: settled.contains state = False) (within: graph.within state = True):
    graph.searchFrom queue settled (Some ((cost, state), rest)) found
      = graph.searchFrom (pushEdges cost (graph.edges state) rest) (settled.insert state cost) (pushEdges cost (graph.edges state) rest).popMin rfl :=
  rewrite Graph.searchFrom.unfold graph queue settled (Some ((cost, state), rest)) found in
    Decidable.elimEq _ _ _ _ (isFresh => Decidable.elimEq _ _ _ _ (isWithin => rfl) (notWithin => Void.exfalso (notWithin within)))
      (notFresh => Void.exfalso (notFresh fresh))

-- A cost the search still has to account for: the pair is queued, or the
-- state is settled for no more.
def Pending [auto ord: Ord s] (queue: Set (Nat, s)) (settled: Map s Nat) (cost: Nat) (state: s): Prop :=
  Or (queue.contains (cost, state) = True) (Exists Nat (found => And (settled.get state = Some found) (found ≤ cost)))

-- The state is settled for no more than `cost`.
def Bound [auto ord: Ord s] (settled: Map s Nat) (cost: Nat) (state: s): Prop :=
  Exists Nat (found => And (settled.get state = Some found) (found ≤ cost))

-- What holds at each step of the search, for a `reach` that holds at the
-- sources and along every edge: every queued pair and settled state is
-- reached for its cost; each source, and each edge out of a settled state,
-- is pending; nothing settled costs more than anything queued; and queued
-- states are within the graph.
def SearchState [auto ord: Ord s] (graph: Graph s) (sources: List (s, Nat)) (reach: s → Nat → Prop) (queue: Set (Nat, s)) (settled: Map s Nat):
    Prop :=
  And ((cost: Nat) → (state: s) → queue.contains (cost, state) = True → And (reach state cost) (graph.within state = True))
    (And ((state: s) → (cost: Nat) → settled.get state = Some cost → reach state cost)
      (And ((source: s) → (start: Nat) → (source, start) ∈ sources → Pending queue settled start source)
        (And
          ((state: s) → (cost: Nat) → settled.get state = Some cost → (next: s) → (weight: Nat) → (next, weight) ∈ graph.edges state →
            Pending queue settled (cost + weight) next)
          ((state: s) → (cost: Nat) → settled.get state = Some cost → (other: Nat) → (otherState: s) →
            queue.contains (other, otherState) = True → cost ≤ other))))

-- What the search returns: each settled state reached for its cost, each
-- source settled for no more than its starting cost, and each edge out of a
-- settled state leading to one settled for no more than the two together.
def SearchResult [auto ord: Ord s] (graph: Graph s) (sources: List (s, Nat)) (reach: s → Nat → Prop) (result: Map s Nat): Prop :=
  And ((state: s) → (cost: Nat) → result.get state = Some cost → reach state cost)
    (And ((source: s) → (start: Nat) → (source, start) ∈ sources → Bound result start source)
      ((state: s) → (cost: Nat) → result.get state = Some cost → (next: s) → (weight: Nat) → (next, weight) ∈ graph.edges state →
        Bound result (cost + weight) next))

-- A pending cost stays pending when the queue keeps all but the popped
-- pair, the settled states stay, and the popped state is settled for no
-- more than the popped cost.
theorem pendingKept [auto ord: Ord s] (queue: Set (Nat, s)) (newQueue: Set (Nat, s)) (settled: Map s Nat) (newSettled: Map s Nat)
    (poppedCost: Nat) (poppedState: s) (poppedFound: Nat)
    (kept: (entry: (Nat, s)) → queue.contains entry = True → Not (entry = (poppedCost, poppedState)) → newQueue.contains entry = True)
    (stays: (state: s) → (found: Nat) → settled.get state = Some found → newSettled.get state = Some found)
    (popped: newSettled.get poppedState = Some poppedFound) (cheaper: poppedFound ≤ poppedCost)
    (cost: Nat) (state: s) (pending: Pending queue settled cost state): Pending newQueue newSettled cost state :=
  match pending with
    | Inr (Witness found (Both got le)) => Inr (Witness found (Both (stays state found got) le))
    | Inl there =>
      match same: (cost, state) == (poppedCost, poppedState) with
        | True =>
          let equal := DecEq.sound _ _ same
          Inr (Witness poppedFound (Both (rewrite Eq.cong Pair.snd equal in popped) (rewrite Eq.cong Pair.fst equal in cheaper)))
        | False => Inl (kept (cost, state) there (DecEq.soundFalse _ _ same))

-- With nothing queued, a pending cost is a bound.
theorem boundOfPending [auto ord: Ord s] (queue: Set (Nat, s)) (settled: Map s Nat) (empty: queue.popMin = None) (cost: Nat) (state: s)
    (pending: Pending queue settled cost state): Bound settled cost state :=
  match pending with
    | Inr bound => bound
    | Inl there =>
      Void.exfalso (Bool.falseNotTrue (Eq.trans (Eq.sym (missingOfMinNone queue (Set.popMinNone queue empty) (cost, state))) there))

-- Dropping a popped pair whose state is settled keeps the search state.
theorem skipKeeps [auto ord: Ord s] (graph: Graph s) (sources: List (s, Nat)) (reach: s → Nat → Prop) (queue: Set (Nat, s)) (settled: Map s Nat)
    (cost: Nat) (state: s) (found: queue.min = Some (cost, state)) (taken: settled.contains state = True)
    (invariant: SearchState graph sources reach queue settled): SearchState graph sources reach (queue.remove (cost, state)) settled :=
  let (Both queued (Both settledReached (Both sourcesPending (Both edgesPending ordered)))) := invariant
  let inQueue := Set.containsMin queue (cost, state) found
  Exists.elim (getOfContains settled state taken) (settledCost got =>
    let cheaper := ordered state settledCost got cost state inQueue
    let keep := pendingKept queue (queue.remove (cost, state)) settled settled cost state settledCost
      (entry there apart => containsRemoveKeeps queue (cost, state) entry apart there) (other value got => got) got cheaper
    Both (other otherState there => queued other otherState (containsOfRemove queue (cost, state) (other, otherState) there))
      (Both settledReached
        (Both (source start member => keep start source (sourcesPending source start member))
          (Both
            (from fromCost got next weight edge => keep (fromCost + weight) next (edgesPending from fromCost got next weight edge))
            (from fromCost got other otherState there =>
              ordered from fromCost got other otherState (containsOfRemove queue (cost, state) (other, otherState) there))))))

-- Settling the popped state and queueing its edges keeps the search state.
theorem settleKeeps [auto ord: Ord s] (graph: Graph s) (sources: List (s, Nat)) (reach: s → Nat → Prop)
    (edgesReach: (state: s) → (cost: Nat) → reach state cost → (next: s) → (weight: Nat) → (next, weight) ∈ graph.edges state →
      reach next (cost + weight))
    (edgesWithin: (state: s) → graph.within state = True → (next: s) → (weight: Nat) → (next, weight) ∈ graph.edges state →
      graph.within next = True)
    (queue: Set (Nat, s)) (settled: Map s Nat) (cost: Nat) (state: s) (found: queue.min = Some (cost, state))
    (fresh: settled.contains state = False) (invariant: SearchState graph sources reach queue settled):
    SearchState graph sources reach (pushEdges cost (graph.edges state) (queue.remove (cost, state))) (settled.insert state cost) :=
  let (Both queued (Both settledReached (Both sourcesPending (Both edgesPending ordered)))) := invariant
  let rest := queue.remove (cost, state)
  let pushed := pushEdges cost (graph.edges state) rest
  let inQueue := Set.containsMin queue (cost, state) found
  let (Both reached within) := queued cost state inQueue
  let poppedGot: (settled.insert state cost).get state = Some cost := Map.getInsert state cost settled
  let keep := pendingKept queue pushed settled (settled.insert state cost) cost state cost
    (entry there apart => containsPushedKeeps cost (graph.edges state) rest entry (containsRemoveKeeps queue (cost, state) entry apart there))
    (other value got => getInsertKeeps settled state cost fresh other value got) poppedGot (Nat.leRefl cost)
  let atLeast: (other: Nat) → (otherState: s) → pushed.contains (other, otherState) = True → cost ≤ other :=
    other otherState there =>
      match containsPushed cost (graph.edges state) rest other otherState there with
        | Inl inRest => minLeast queue cost state found other otherState (containsOfRemove queue (cost, state) (other, otherState) inRest)
        | Inr (Witness weight (Both edge costs)) => rewrite costs in omega
  Both
    (other otherState there =>
      match containsPushed cost (graph.edges state) rest other otherState there with
        | Inl inRest => queued other otherState (containsOfRemove queue (cost, state) (other, otherState) inRest)
        | Inr (Witness weight (Both edge costs)) =>
          rewrite costs in Both (edgesReach state cost reached otherState weight edge) (edgesWithin state within otherState weight edge))
    (Both
      (other otherCost got =>
        match getInsertCases settled state cost other otherCost got with
          | Inl (Both same costs) => rewrite same, costs in reached
          | Inr old => settledReached other otherCost old)
      (Both (source start member => keep start source (sourcesPending source start member))
        (Both
          (from fromCost got next weight edge =>
            match getInsertCases settled state cost from fromCost got with
              | Inl (Both same costs) =>
                rewrite costs in Inl (containsPushedEdge cost (graph.edges state) rest next weight (rewrite <- same in edge))
              | Inr old => keep (fromCost + weight) next (edgesPending from fromCost old next weight edge))
          (from fromCost got other otherState there =>
            match getInsertCases settled state cost from fromCost got with
              | Inl (Both same costs) => rewrite costs in atLeast other otherState there
              | Inr old => omega [ordered from fromCost old cost state inQueue, atLeast other otherState there]))))

-- The search returns what `SearchResult` says, from any search state.
theorem searchFromCorrect [auto ord: Ord s] (graph: Graph s) (sources: List (s, Nat)) (reach: s → Nat → Prop)
    (edgesReach: (state: s) → (cost: Nat) → reach state cost → (next: s) → (weight: Nat) → (next, weight) ∈ graph.edges state →
      reach next (cost + weight))
    (edgesWithin: (state: s) → graph.within state = True → (next: s) → (weight: Nat) → (next, weight) ∈ graph.edges state →
      graph.within next = True)
    (queue: Set (Nat, s)) (settled: Map s Nat):
    (popped: Option ((Nat, s), Set (Nat, s))) → (found: queue.popMin = popped) → SearchState graph sources reach queue settled →
      SearchResult graph sources reach (graph.searchFrom queue settled popped found)
    decreasing (graph.unsettled settled, queue.size)
  | None, found, invariant =>
    rewrite searchEmpty graph queue settled found in
      let (Both queued (Both settledReached (Both sourcesPending (Both edgesPending ordered)))) := invariant
      Both settledReached
        (Both (source start member => boundOfPending queue settled found start source (sourcesPending source start member))
          (from fromCost got next weight edge =>
            boundOfPending queue settled found (fromCost + weight) next (edgesPending from fromCost got next weight edge)))
  | Some ((cost, state), rest), found, invariant =>
    let (Both least restIs) := Set.popMinSome queue (cost, state) rest found
    match taken: settled.contains state with
      | True =>
        rewrite searchSkip graph queue settled cost state rest found taken in
          searchFromCorrect graph sources reach edgesReach edgesWithin rest settled rest.popMin rfl
            (rewrite restIs in skipKeeps graph sources reach queue settled cost state least taken invariant)
            [decreasing := Nat.LexLess.Second rfl (Set.sizePopMin queue (cost, state) rest found)]
      | False =>
        let within := And.right (And.left invariant cost state (Set.containsMin queue (cost, state) least))
        rewrite searchSettle graph queue settled cost state rest found taken within in
          searchFromCorrect graph sources reach edgesReach edgesWithin (pushEdges cost (graph.edges state) rest) (settled.insert state cost)
            (pushEdges cost (graph.edges state) rest).popMin rfl
            (rewrite restIs in settleKeeps graph sources reach edgesReach edgesWithin queue settled cost state least taken invariant)
            [decreasing := Nat.LexLess.First (unsettledInsert graph settled state cost (graph.listed state within) taken)]

-- The distances from the sources: each reached for its cost, each source
-- settled for no more than its starting cost, and each edge out of a
-- settled state leading to one settled for no more than the two together.
theorem distancesCorrect [auto ord: Ord s] (graph: Graph s) (sources: List (s, Nat)) (reach: s → Nat → Prop)
    (sourcesReach: (source: s) → (start: Nat) → (source, start) ∈ sources → reach source start)
    (sourcesWithin: (source: s) → (start: Nat) → (source, start) ∈ sources → graph.within source = True)
    (edgesReach: (state: s) → (cost: Nat) → reach state cost → (next: s) → (weight: Nat) → (next, weight) ∈ graph.edges state →
      reach next (cost + weight))
    (edgesWithin: (state: s) → graph.within state = True → (next: s) → (weight: Nat) → (next, weight) ∈ graph.edges state →
      graph.within next = True):
    SearchResult graph sources reach (graph.distances sources) :=
  let queue := pushEdges 0 sources Set.empty
  let initial: SearchState graph sources reach queue Map.empty :=
    Both
      (cost state there =>
        match containsPushed 0 sources Set.empty cost state there with
          | Inl none => Void.exfalso (Bool.falseNotTrue none)
          | Inr (Witness start (Both member costs)) =>
            let same: cost = start := omega
            rewrite same in Both (sourcesReach state start member) (sourcesWithin state start member))
      (Both (state cost got => Void.exfalso (Option.noneNotSome cost got))
        (Both
          (source start member =>
            let same: 0 + start = start := omega
            Inl (rewrite <- same in containsPushedEdge 0 sources Set.empty source start member))
          (Both (state cost got => Void.exfalso (Option.noneNotSome cost got)) (state cost got => Void.exfalso (Option.noneNotSome cost got)))))
  searchFromCorrect graph sources reach edgesReach edgesWithin queue Map.empty queue.popMin rfl initial
