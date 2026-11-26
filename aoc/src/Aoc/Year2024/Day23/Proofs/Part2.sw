--| Part 2: the search returns a set of computers all connected to each other
--| (soundness) and no such set is larger (optimality), for every network
--| (`largestCorrect`, `part2Correct`).
--|
--| The search's invariant (`largestFromAnswers`): given a clique, candidates
--| each connected to all of it, and a clique `best` found so far, the result
--| is a clique, no smaller than `best`, and no smaller than any clique made of
--| the clique and some of the candidates.
--
-- A clique holding the smallest candidate is made of the clique, that
-- candidate and some of its neighbours among the other candidates (the
-- first search); one without it is made of the clique and the other
-- candidates (the second).

namespace Aoc.Year2024.Day23.Proofs
import Aoc.Year2024.Day23 (..)
import Aoc.Year2024.Day23.Spec (..)
import Std (And, Bool, Eq, Exists, Iff, List, Nat, Not, Option, Or, Set, Void)

--| The program's reading of a clique: every member has links, and every two
--| different members are neighbours.
def Clique (network: Network) (set: Set Computer): Prop :=
  (∀ (member: Computer) => set.contains member = True → network.links.keySet.contains member = True)
    ∧ (∀ (one other: Computer) => set.contains one = True
      → set.contains other = True
      → one ≠ other
      → (network.links.neighbours one).contains other = True)

--| Each candidate has links, isn't in the clique yet, and is a neighbour of
--| all of it.
def Candidates (network: Network) (clique candidates: Set Computer): Prop :=
  ∀ (candidate: Computer) => candidates.contains candidate = True
    → network.links.keySet.contains candidate = True
      ∧ clique.contains candidate = False
      ∧ (∀ (member: Computer) => clique.contains member = True
        → (network.links.neighbours candidate).contains member = True)

--| Every computer in `small` is in `big`.
def Within (small big: Set Computer): Prop := ∀ (key: Computer) => small.contains key = True → big.contains key = True

--| What `Links.largestFrom` returns: a clique, no smaller than `best`, and no
--| smaller than any clique holding `clique` within `clique` and the
--| candidates.
def Answers (network: Network) (clique candidates best result: Set Computer): Prop :=
  Clique network result
    ∧ best.size ≤ result.size
    ∧ (∀ (other: Set Computer) => Clique network other
      → Within clique other
      → Within other (clique.union candidates)
      → other.size ≤ result.size)

--| The clique and its candidates have no computer in common.
theorem sizeCliqueAndCandidates ∀ (network: Network) (clique candidates: Set Computer)
    (candidatesOk: Candidates network clique candidates):
    (clique.union candidates).size = clique.size + candidates.size :=
  Set.sizeUnionDisjoint clique candidates (key inClique =>
    match isCandidate: candidates.contains key with
      | False => byComputing
      | True =>
        Void.impossible (Bool.falseNotTrue (Eq.trans (Eq.flipped (candidatesOk key isCandidate).right.left) inClique)))

--| In a union, a key is in one side or the other.
theorem unionElim ∀ (one other: Set Computer) (key: Computer) (goal: Prop)
    (held: (one.union other).contains key = True)
    (left: one.contains key = True → goal) (right: other.contains key = True → goal):
    goal :=
  match Eq.trans (Set.containsUnion one key other).flipped held with
    | Inl inOne => left inOne
    | Inr inOther => right inOther

--| After an insert, a set holds the key inserted or what it held before.
theorem insertElim ∀ (set: Set Computer) (inserted key: Computer) (goal: Prop)
    (held: (set.insert inserted).contains key = True)
    (same: key = inserted → goal) (before: set.contains key = True → goal):
    goal :=
  match Set.containsInsertElim set inserted key held with
    | Inl isInserted => same isInserted
    | Inr wasThere => before wasThere

theorem intersectElim ∀ (one other: Set Computer) (key: Computer)
    (held: (one.intersect other).contains key = True):
    one.contains key = True ∧ other.contains key = True :=
  let (Both inOne inOther) := Eq.trans (Eq.flipped (Set.containsIntersect one key other)) held
  Both inOne inOther

--| With nothing to pop, a set holds nothing.
theorem noneHeld ∀ (set: Set Computer)
    (found: set.popMin = None) (key: Computer)
    (held: set.contains key = True):
    Void :=
  let least := Set.popMinNone set found
  let listed: List.Mem key set.toList := held.read
  match keys: set.toList with
    | [first, ..rest] => Option.someNotNone first (Eq.trans (Eq.flipped (rewrite Set.minToList set, keys)) least)

theorem sizeNone ∀ (set: Set Computer) (found: set.popMin = None): set.size = 0 :=
  rewrite Set.sizeToList set then
    match keys: set.toList with
      | [] => byComputing
      | [first, ..rest] =>
        Void.impossible
          (noneHeld set found first ((Set.memToList set first).forward (rewrite keys then Inl byComputing)))

--| The other candidates are the candidates other than the smallest.
theorem othersElim ∀ (candidates: Set Computer) (candidate: Computer) (others: Set Computer)
    (othersAre: others = candidates.remove candidate) (key: Computer)
    (held: others.contains key = True):
    candidates.contains key = True ∧ key ≠ candidate :=
  if same: key = candidate then
    Void.impossible
      (Bool.falseNotTrue
        (Eq.trans (Eq.flipped (Set.containsRemove candidates candidate)) (rewrite othersAre, same at held)))
  else Both (rewrite othersAre, Set.containsRemoveOther candidates candidate key same at held) same

theorem othersIntro ∀ (candidates: Set Computer) (candidate: Computer) (others: Set Computer)
    (othersAre: others = candidates.remove candidate) (key: Computer)
    (held: candidates.contains key = True)
    (different: key ≠ candidate):
    others.contains key = True :=
  rewrite othersAre, Set.containsRemoveOther candidates candidate key different then held

--| A candidate added to the clique keeps it a clique.
theorem cliqueInsert ∀ (network: Network) (clique: Set Computer) (candidate: Computer)
    (cliqueOk: Clique network clique)
    (candidateLinked: network.links.keySet.contains candidate = True)
    (candidateNeighbours: ∀ (member: Computer) => clique.contains member = True
      → (network.links.neighbours candidate).contains member = True):
    Clique network (clique.insert candidate) :=
  Both
    (member held =>
      insertElim clique candidate member
        (network.links.keySet.contains member = True)
        held
        (same => rewrite same then candidateLinked)
        (inClique => cliqueOk.left member inClique))
    (one other heldOne heldOther different =>
      insertElim clique candidate one
        ((network.links.neighbours one).contains other = True)
        heldOne
        (oneIs =>
          insertElim clique candidate other
            ((network.links.neighbours one).contains other = True)
            heldOther
            (otherIs => Void.impossible (different (Eq.trans oneIs otherIs.flipped)))
            (otherInClique => rewrite oneIs then candidateNeighbours other otherInClique))
        (oneInClique =>
          insertElim clique candidate other
            ((network.links.neighbours one).contains other = True)
            heldOther
            (otherIs =>
              rewrite otherIs then linkedSymmetric network candidate one (candidateNeighbours one oneInClique))
            (otherInClique => cliqueOk.right one other oneInClique otherInClique different)))

--| With the candidate in the clique, its neighbours among the other
--| candidates are the candidates.
theorem candidatesNarrowed ∀ (network: Network) (clique candidates: Set Computer)
    (candidate: Computer) (others: Set Computer)
    (candidatesOk: Candidates network clique candidates)
    (othersAre: others = candidates.remove candidate):
    Candidates network (clique.insert candidate) (network.links.neighbours candidate |> .intersect others) :=
  key held =>
    let (Both neighbour inOthers) := intersectElim (network.links.neighbours candidate) others key held
    let (Both wasCandidate notCandidate) := othersElim candidates candidate others othersAre key inOthers
    let (Both keyLinked (Both keyOutside keyNeighbours)) := candidatesOk key wasCandidate
    Both keyLinked
      (Both (rewrite Set.containsInsertOther clique candidate key notCandidate then keyOutside) (member inserted =>
        insertElim clique candidate member
          ((network.links.neighbours key).contains member = True)
          inserted
          (memberIs => rewrite memberIs then linkedSymmetric network candidate key neighbour)
          (inClique => keyNeighbours member inClique)))

--| A clique holding the candidate is within the clique, the candidate and
--| its neighbours among the other candidates.
theorem withinWithCandidate ∀ (network: Network) (clique candidates: Set Computer)
    (candidate: Computer) (others: Set Computer)
    (othersAre: others = candidates.remove candidate) (other: Set Computer)
    (otherOk: Clique network other)
    (has: other.contains candidate = True)
    (within: Within other (clique.union candidates)):
    Within other ((clique.insert candidate).union (network.links.neighbours candidate |> .intersect others)) :=
  key held =>
    let narrowed := network.links.neighbours candidate |> .intersect others
    unionElim clique candidates key
      (((clique.insert candidate).union narrowed).contains key = True)
      (within key held)
      (inClique =>
        Set.containsUnionLeft
          (clique.insert candidate)
          narrowed
          key
          (Set.containsInsertMono clique candidate key inClique))
      (wasCandidate =>
        if same: key = candidate then
          Set.containsUnionLeft
            (clique.insert candidate)
            narrowed
            key
            (rewrite same then Set.containsInsert candidate clique)
        else
          let inOthers := othersIntro candidates candidate others othersAre key wasCandidate same
          let neighbour := otherOk.right candidate key has held (isSame => same isSame.flipped)
          Set.containsUnionRight
            (clique.insert candidate)
            narrowed
            key
            (rewrite Set.containsIntersect (network.links.neighbours candidate) key others, neighbour, inOthers))

--| A clique without the candidate is within the clique and the other
--| candidates.
theorem withinWithoutCandidate ∀ (clique candidates: Set Computer) (candidate: Computer) (others: Set Computer)
    (othersAre: others = candidates.remove candidate) (other: Set Computer)
    (hasNot: other.contains candidate = False)
    (within: Within other (clique.union candidates)):
    Within other (clique.union others) :=
  key held =>
    unionElim clique candidates key
      ((clique.union others).contains key = True)
      (within key held)
      (inClique => Set.containsUnionLeft clique others key inClique)
      (wasCandidate =>
        if same: key = candidate then
          Void.impossible (Bool.falseNotTrue (Eq.trans hasNot.flipped (rewrite <- same then held)))
        else
          Set.containsUnionRight clique others key
            (othersIntro candidates candidate others othersAre key wasCandidate same))

theorem largestFromAnswers ∀ (network: Network) (clique candidates best: Set Computer)
    (cliqueOk: Clique network clique)
    (candidatesOk: Candidates network clique candidates)
    (bestOk: Clique network best):
    Answers network clique candidates best (network.links.largestFrom clique candidates best)
    decreasing candidates.size
:=
  match fits: Nat.leq (clique.size + candidates.size) best.size with
    | True =>
      let joined := sizeCliqueAndCandidates network clique candidates candidatesOk
      rewrite largestPruned network.links clique candidates best (arithmetic [fits]) then
        Both bestOk
          (Both (arithmetic) (other otherOk inside within =>
            arithmetic [Set.sizeSubset (clique.union candidates) other within, joined, fits]))
    | False =>
      match found: candidates.popMin with
        | None =>
          rewrite largestDone network.links clique candidates best (arithmetic [fits]) found then
            Both cliqueOk
              (Both (arithmetic [fits, sizeNone candidates found]) (other otherOk inside within =>
                Set.sizeSubset clique other (key held =>
                  unionElim clique candidates key
                    (clique.contains key = True)
                    (within key held)
                    (inClique => inClique)
                    (isCandidate => Void.impossible (noneHeld candidates found key isCandidate)))))
        | Some (candidate, others) =>
          let (Both least othersAre) := Set.popMinSome candidates candidate others found
          let (Both candidateLinked (Both candidateOutside candidateNeighbours)) :=
            candidatesOk candidate (Set.containsMin candidates candidate least)
          let narrowed := network.links.neighbours candidate |> .intersect others
          let withinOthers: narrowed.size ≤ others.size := Set.sizeSubset others narrowed (key held =>
            (intersectElim (network.links.neighbours candidate) others key held).right)
          let fewer := Set.sizePopMin candidates candidate others found
          let withIt := network.links.largestFrom (clique.insert candidate) narrowed best
          let withItOk: Answers network (clique.insert candidate) narrowed best withIt :=
            largestFromAnswers network
              (clique.insert candidate)
              narrowed
              best
              (cliqueInsert network clique candidate cliqueOk candidateLinked candidateNeighbours)
              (candidatesNarrowed network clique candidates candidate others candidatesOk othersAre)
              bestOk
              [decreasing := arithmetic [withinOthers, fewer]]
          let restOk: Answers network clique others withIt (network.links.largestFrom clique others withIt) :=
            largestFromAnswers network clique others withIt cliqueOk
              (key held => candidatesOk key (othersElim candidates candidate others othersAre key held).left)
              withItOk.left
              [decreasing := arithmetic [fewer]]
          rewrite largestStep network.links clique candidates best (arithmetic [fits]) candidate others found then
            Both restOk.left
              (Both (arithmetic [withItOk.right.left, restOk.right.left]) (other otherOk inside within =>
                match has: other.contains candidate with
                  | True =>
                    let insideWith: Within (clique.insert candidate) other := key held =>
                      insertElim clique candidate key
                        (other.contains key = True)
                        held
                        (same => rewrite same then has)
                        (inClique => inside key inClique)
                    arithmetic [
                      withItOk.right.right other otherOk insideWith
                        (withinWithCandidate network clique candidates candidate others othersAre other otherOk has
                            within),
                      restOk.right.left
                    ]
                  | False =>
                    restOk.right.right other otherOk inside
                      (withinWithoutCandidate clique candidates candidate others othersAre other has within)))

theorem emptyClique ∀ (network: Network): Clique network Set.empty :=
  Both (member held => cases) (one other heldOne heldOther different => cases)

--| At the start, every computer with links is a candidate.
theorem allCandidates ∀ (network: Network): Candidates network Set.empty network.links.keySet := candidate held =>
  Both held (Both byComputing (member inEmpty => cases))

--| The puzzle's cliques are the program's.
theorem cliqueOfSpec ∀ (network: Network) (party: Party) (spec: IsClique network party): Clique network party.members :=
  Both
    (member held => (hasLinksIff network member).backward (spec.left member held))
    (one other heldOne heldOther different =>
      (linkedIff network one other).backward (spec.right one other heldOne heldOther different))

theorem specOfClique ∀ (network: Network) (party: Party)
    (clique: Clique network party.members):
    IsClique network party :=
  Both
    (member held => (hasLinksIff network member).forward (clique.left member held))
    (one other heldOne heldOther different =>
      (linkedIff network one other).forward (clique.right one other heldOne heldOther different))

--| "the largest set of computers that are all connected to each other".
theorem largestCorrect ∀ (network: Network): IsLargest network (network.links.largestClique) :=
  let answers :=
    largestFromAnswers network Set.empty network.links.keySet Set.empty
      (emptyClique network)
      (allCandidates network)
      (emptyClique network)
  Both (specOfClique network (network.links.largestClique) answers.left) (other otherSpec =>
    let otherOk := cliqueOfSpec network other otherSpec
    answers.right.right other.members otherOk (key held => cases) (key held =>
      Set.containsUnionRight Set.empty network.links.keySet key (otherOk.left key held)))

theorem part2Correct ∀ (network: Network): IsPart2 network (solvePart2 network) :=
  Witness (network.links.largestClique) (Both (largestCorrect network) byComputing)
