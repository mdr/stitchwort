-- Part 2: the search returns a set of computers all connected to each other
-- (soundness) and no such set is larger (optimality), for every network
-- (`largestCorrect`, `part2Correct`).
--
-- The search's invariant (`largestFromAnswers`): given a clique, candidates
-- each connected to all of it, and a clique `best` found so far, the result
-- is a clique, no smaller than `best`, and no smaller than any clique made of
-- the clique and some of the candidates. A clique holding the smallest
-- candidate is made of the clique, that candidate and some of its
-- neighbours among the other candidates (the first search); one without it
-- is made of the clique and the other candidates (the second).

namespace Aoc.Year2024.Day23.Proofs
import Aoc.Year2024.Day23 (..)
import Aoc.Year2024.Day23.Spec (..)
import Std (And, Bool, Eq, Exists, Iff, List, Nat, Not, Option, Or, Set, Void)

-- The program's reading of a clique: every member has links, and every two
-- different members are neighbours.
def Clique (network: Network) (set: Set Computer): Prop :=
  ((member: Computer) → set.contains member = True → network.links.keySet.contains member = True)
    ∧ ((one: Computer) → (other: Computer) → set.contains one = True → set.contains other = True → Not (one = other) →
      (neighbours network.links one).contains other = True)

-- Each candidate has links, isn't in the clique yet, and is a neighbour of
-- all of it.
def Candidates (network: Network) (clique: Set Computer) (candidates: Set Computer): Prop :=
  (candidate: Computer) → candidates.contains candidate = True →
    network.links.keySet.contains candidate = True
      ∧ clique.contains candidate = False
      ∧ ((member: Computer) → clique.contains member = True → (neighbours network.links candidate).contains member = True)

-- Every computer in `small` is in `big`.
def Within (small: Set Computer) (big: Set Computer): Prop := (key: Computer) → small.contains key = True → big.contains key = True

-- What `largestFrom` returns: a clique, no smaller than `best`, and no
-- smaller than any clique holding `clique` within `clique` and the
-- candidates.
def Answers (network: Network) (clique: Set Computer) (candidates: Set Computer) (best: Set Computer) (result: Set Computer): Prop :=
  Clique network result
    ∧ best.size ≤ result.size
    ∧ ((other: Set Computer) → Clique network other → Within clique other → Within other (clique.union candidates) → other.size ≤ result.size)

theorem sizeWithin (small: Set Computer) (big: Set Computer) (within: Within small big): small.size ≤ big.size := Set.sizeSubset big small within

-- The clique and its candidates have no computer in common.
theorem sizeCliqueAndCandidates (network: Network) (clique: Set Computer) (candidates: Set Computer) (candidatesOk: Candidates network clique candidates):
    (clique.union candidates).size = clique.size + candidates.size :=
  Set.sizeUnionDisjoint clique candidates (key inClique =>
    match isCandidate: candidates.contains key with
      | False => rfl
      | True => Void.exfalso (Bool.falseNotTrue (Eq.trans (Eq.sym (candidatesOk key isCandidate).right.left) inClique)))

-- In a union, a key is in one side or the other.
theorem unionElim (one: Set Computer) (other: Set Computer) (key: Computer) (goal: Prop) (held: (one.union other).contains key = True)
    (left: one.contains key = True → goal) (right: other.contains key = True → goal): goal :=
  Bool.orElim (one.contains key) (other.contains key) goal (rewrite <- Set.containsUnion one key other in held) left right

-- After an insert, a set holds the key inserted or what it held before.
theorem insertElim (set: Set Computer) (inserted: Computer) (key: Computer) (goal: Prop) (held: (set.insert inserted).contains key = True)
    (same: key = inserted → goal) (before: set.contains key = True → goal): goal :=
  match Set.containsInsertElim set inserted key held with
    | Inl isInserted => same isInserted
    | Inr wasThere => before wasThere

theorem intersectElim (one: Set Computer) (other: Set Computer) (key: Computer) (held: (one.intersect other).contains key = True):
    one.contains key = True ∧ other.contains key = True :=
  let both := Eq.trans (Eq.sym (Set.containsIntersect one key other)) held
  Both (Bool.andLeft _ _ both) (Bool.andRight _ _ both)

-- With nothing to pop, a set holds nothing.
theorem noneHeld (set: Set Computer) (found: set.popMin = None) (key: Computer) (held: set.contains key = True): Void :=
  let least := Set.popMinNone set found
  let listed := (Set.memToList set key).backward held
  match keys: set.toList with
    | Nil => listed
    | Cons first rest => Option.someNotNone first (Eq.trans (Eq.sym (rewrite Set.minToList set, keys in rfl)) least)

theorem sizeNone (set: Set Computer) (found: set.popMin = None): set.size = 0 :=
  rewrite Set.sizeToList set in
  match keys: set.toList with
    | Nil => rfl
    | Cons first rest => Void.exfalso (noneHeld set found first ((Set.memToList set first).forward (rewrite keys in Inl rfl)))

theorem largestFromAnswers (network: Network) (clique: Set Computer) (candidates: Set Computer) (best: Set Computer)
    (cliqueOk: Clique network clique) (candidatesOk: Candidates network clique candidates) (bestOk: Clique network best):
    Answers network clique candidates best (largestFrom network.links clique candidates best)
    decreasing candidates.size
:=
  let joined := sizeCliqueAndCandidates network clique candidates candidatesOk
  match fits: Nat.leq (clique.size + candidates.size) best.size with
    | True =>
      let pruned: clique.size + candidates.size ≤ best.size := omega [fits]
      rewrite largestPruned network.links clique candidates best pruned in
      Both bestOk
        (Both (omega) (other otherOk inside within => omega [sizeWithin other (clique.union candidates) within, joined, pruned]))
    | False =>
      match found: candidates.popMin with
        | None =>
          let empty := sizeNone candidates found
          rewrite largestDone network.links clique candidates best (omega [fits]) found in
          Both cliqueOk
            (Both (omega [fits, empty])
              (other otherOk inside within =>
                sizeWithin other clique (key held =>
                  unionElim clique candidates key (clique.contains key = True) (within key held) (inClique => inClique)
                    (isCandidate => Void.exfalso (noneHeld candidates found key isCandidate)))))
        | Some (candidate, others) =>
          let (Both least othersAre) := Set.popMinSome candidates candidate others found
          let isCandidate := Set.containsMin candidates candidate least
          let (Both candidateLinked (Both candidateOutside candidateNeighbours)) := candidatesOk candidate isCandidate
          let fewer := Set.sizePopMin candidates candidate others found
          -- The other candidates are candidates other than the smallest.
          let otherOf: (key: Computer) → others.contains key = True → candidates.contains key = True ∧ Not (key = candidate) :=
            key held =>
              match DecEq.decide key candidate with
                | Yes same =>
                  Void.exfalso (Bool.falseNotTrue (Eq.trans (Eq.sym (Set.containsRemove candidates candidate)) (rewrite othersAre, same at held)))
                | No same => Both (rewrite othersAre, Set.containsRemoveOther candidates candidate key same at held) same
          let narrowed := neighbours network.links candidate |> .intersect others
          let withinOthers: narrowed.size ≤ others.size :=
            Set.sizeSubset others narrowed (key held => (intersectElim (neighbours network.links candidate) others key held).right)
          let cliqueWith: Clique network (clique.insert candidate) :=
            Both
              (member held =>
                insertElim clique candidate member (network.links.keySet.contains member = True) held (same => rewrite same in candidateLinked)
                  (inClique => cliqueOk.left member inClique))
              (one other heldOne heldOther different =>
                insertElim clique candidate one ((neighbours network.links one).contains other = True) heldOne
                  (oneIs =>
                    insertElim clique candidate other ((neighbours network.links one).contains other = True) heldOther
                      (otherIs => Void.exfalso (different (Eq.trans oneIs (Eq.sym otherIs))))
                      (otherInClique => rewrite oneIs in candidateNeighbours other otherInClique))
                  (oneInClique =>
                    insertElim clique candidate other ((neighbours network.links one).contains other = True) heldOther
                      (otherIs => rewrite otherIs in linkedSymmetric network candidate one (candidateNeighbours one oneInClique))
                      (otherInClique => cliqueOk.right one other oneInClique otherInClique different)))
          let candidatesWith: Candidates network (clique.insert candidate) narrowed :=
            key held =>
              let (Both neighbour inOthers) := intersectElim (neighbours network.links candidate) others key held
              let (Both wasCandidate notCandidate) := otherOf key inOthers
              let (Both keyLinked (Both keyOutside keyNeighbours)) := candidatesOk key wasCandidate
              Both keyLinked
                (Both (rewrite Set.containsInsertOther clique candidate key notCandidate in keyOutside)
                  (member inserted =>
                    insertElim clique candidate member ((neighbours network.links key).contains member = True) inserted
                      (memberIs => rewrite memberIs in linkedSymmetric network candidate key neighbour)
                      (inClique => keyNeighbours member inClique)))
          let withIt := largestFrom network.links (clique.insert candidate) narrowed best
          let withItOk: Answers network (clique.insert candidate) narrowed best withIt :=
            largestFromAnswers network (clique.insert candidate) narrowed best cliqueWith candidatesWith bestOk
              [decreasing := omega [withinOthers, fewer]]
          let candidatesRest: Candidates network clique others := key held => candidatesOk key (otherOf key held).left
          let restOk: Answers network clique others withIt (largestFrom network.links clique others withIt) :=
            largestFromAnswers network clique others withIt cliqueOk candidatesRest withItOk.left [decreasing := omega [fewer]]
          rewrite largestStep network.links clique candidates best (omega [fits]) candidate others found in
          Both restOk.left
            (Both (omega [withItOk.right.left, restOk.right.left])
              (other otherOk inside within =>
                match has: other.contains candidate with
                  | True =>
                    let insideWith: Within (clique.insert candidate) other :=
                      key held => insertElim clique candidate key (other.contains key = True) held (same => rewrite same in has) (inClique => inside key inClique)
                    let withinWith: Within other ((clique.insert candidate).union narrowed) :=
                      key held =>
                        unionElim clique candidates key (((clique.insert candidate).union narrowed).contains key = True) (within key held)
                          (inClique => Set.containsUnionLeft (clique.insert candidate) narrowed key (Set.containsInsertMono clique candidate key inClique))
                          (wasCandidate =>
                            match DecEq.decide key candidate with
                              | Yes same =>
                                Set.containsUnionLeft (clique.insert candidate) narrowed key (rewrite same in Set.containsInsert candidate clique)
                              | No same =>
                                let inOthers: others.contains key = True :=
                                  rewrite othersAre, Set.containsRemoveOther candidates candidate key same in wasCandidate
                                let neighbour := otherOk.right candidate key has held (isSame => same (Eq.sym isSame))
                                Set.containsUnionRight (clique.insert candidate) narrowed key
                                  (rewrite Set.containsIntersect (neighbours network.links candidate) key others, neighbour, inOthers in rfl))
                    omega [withItOk.right.right other otherOk insideWith withinWith, restOk.right.left]
                  | False =>
                    restOk.right.right other otherOk inside
                      (key held =>
                        unionElim clique candidates key ((clique.union others).contains key = True) (within key held)
                          (inClique => Set.containsUnionLeft clique others key inClique)
                          (wasCandidate =>
                            match DecEq.decide key candidate with
                              | Yes same => Void.exfalso (Bool.falseNotTrue (Eq.trans (Eq.sym has) (rewrite <- same in held)))
                              | No same =>
                                Set.containsUnionRight clique others key
                                  (rewrite othersAre, Set.containsRemoveOther candidates candidate key same in wasCandidate)))))

theorem emptyClique (network: Network): Clique network Set.empty :=
  Both (member held => Void.exfalso (Bool.falseNotTrue held)) (one other heldOne heldOther different => Void.exfalso (Bool.falseNotTrue heldOne))

-- At the start, every computer with links is a candidate.
theorem allCandidates (network: Network): Candidates network Set.empty network.links.keySet :=
  candidate held => Both held (Both rfl (member inEmpty => Void.exfalso (Bool.falseNotTrue inEmpty)))

-- The puzzle's cliques are the program's.
theorem cliqueOfSpec (network: Network) (set: Set Computer) (spec: IsClique network set): Clique network set :=
  Both (member held => (hasLinksIff network member).backward (spec.left member held))
    (one other heldOne heldOther different => (linkedIff network one other).backward (spec.right one other heldOne heldOther different))

theorem specOfClique (network: Network) (set: Set Computer) (clique: Clique network set): IsClique network set :=
  Both (member held => (hasLinksIff network member).forward (clique.left member held))
    (one other heldOne heldOther different => (linkedIff network one other).forward (clique.right one other heldOne heldOther different))

-- "the largest set of computers that are all connected to each other".
theorem largestCorrect (network: Network): IsLargest network (largestClique network.links) :=
  let answers := largestFromAnswers network Set.empty network.links.keySet Set.empty (emptyClique network) (allCandidates network) (emptyClique network)
  Both (specOfClique network (largestClique network.links) answers.left)
    (other otherSpec =>
      let otherOk := cliqueOfSpec network other otherSpec
      answers.right.right other otherOk (key held => Void.exfalso (Bool.falseNotTrue held))
        (key held => Set.containsUnionRight Set.empty network.links.keySet key (otherOk.left key held)))

theorem part2Correct (network: Network): IsPart2 network (solvePart2 network) := Witness (largestClique network.links) (Both (largestCorrect network) rfl)
