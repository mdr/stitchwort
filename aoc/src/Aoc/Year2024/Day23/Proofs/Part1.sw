-- Part 1: the program's sets of three are the puzzle's (`setsOfThreeIff`),
-- so it counts the sets of three inter-connected computers with a t name,
-- for every network (`part1Correct`).
--
-- A set the program makes is a computer, a neighbour and a neighbour of
-- both, so each is connected to the other two; it keeps those of size 3.
-- Back the other way, a set of size 3 lists as three different computers,
-- the first of which has links; the program makes that set from them.

namespace Aoc.Year2024.Day23.Proofs
import Aoc.Year2024.Day23 (..)
import Aoc.Year2024.Day23.Spec (..)
import Std (And, Bool, DecEq, Eq, Exists, Iff, List, Map, Nat, Not, Or, Set, Void)

theorem sizeThree (set: Set Computer) (three: (set.size == 3) = True): set.size = 3 := DecEq.sound set.size 3 three

-- What the program makes before keeping the sets of three: the sets from
-- each computer with links.
def madeSets (links: Links): List (Set Computer) := links.keySet.toList.flatMap (setsWith links)

-- A set the program makes is three computers, each pair neighbours.
theorem madeElim (network: Network) (set: Set Computer) (made: List.Mem set (madeSets network.links)) (goal: Prop)
    (found: (first: Computer) → (second: Computer) → (third: Computer) → set = Set.fromList [first, second, third] →
      (neighbours network.links first).contains second = True → (neighbours network.links first).contains third = True →
      (neighbours network.links second).contains third = True → goal):
    goal :=
  List.anyElim (first => List.Mem set (setsWith network.links first)) goal network.links.keySet.toList
    (List.memFlatMapElim (setsWith network.links) set network.links.keySet.toList made)
    (first unused fromFirst =>
      let firstNeighbours := neighbours network.links first
      List.anyElim
        (second => List.Mem set (neighbours network.links second |> .intersect firstNeighbours |> .toList |> .map (third => Set.fromList [first, second, third])))
        goal firstNeighbours.toList
        (List.memFlatMapElim
          (second => neighbours network.links second |> .intersect firstNeighbours |> .toList |> .map (third => Set.fromList [first, second, third]))
          set firstNeighbours.toList fromFirst)
        (second secondListed fromSecond =>
          List.anyElim (third => Set.fromList [first, second, third] = set) goal (neighbours network.links second |> .intersect firstNeighbours |> .toList)
            (List.memMapAny (neighbours network.links second |> .intersect firstNeighbours |> .toList) (third => Set.fromList [first, second, third]) set fromSecond)
            (third thirdListed isSet =>
              let (Both secondThird firstThird) :=
                intersectElim (neighbours network.links second) firstNeighbours third
                  ((Set.memToList (neighbours network.links second |> .intersect firstNeighbours) third).forward thirdListed)
              found first second third (Eq.sym isSet) ((Set.memToList firstNeighbours second).forward secondListed) firstThird secondThird)))

-- The sets the program makes are all connected.
theorem madeConnected (network: Network) (set: Set Computer) (made: List.Mem set (madeSets network.links)): AllConnected network set :=
  madeElim network set made (AllConnected network set)
    (first second third isSet firstSecond firstThird secondThird one other heldOne heldOther different =>
      let pair: (one: Computer) → (other: Computer) → (neighbours network.links one).contains other = True → connected network one other = True :=
        one other held => (linkedIff network one other).forward held
      let back: (one: Computer) → (other: Computer) → (neighbours network.links one).contains other = True → connected network other one = True :=
        one other held => (linkedIff network other one).forward (linkedSymmetric network one other held)
      let same: (member: Computer) → one = member → other = member → connected network one other = True :=
        member isOne isOther => Void.exfalso (different (Eq.trans isOne (Eq.sym isOther)))
      threeElim first second third one (connected network one other = True) (rewrite isSet at heldOne)
        (oneIs =>
          threeElim first second third other (connected network one other = True) (rewrite isSet at heldOther) (otherIs => same first oneIs otherIs)
            (otherIs => rewrite oneIs, otherIs in pair first second firstSecond)
            (otherIs => rewrite oneIs, otherIs in pair first third firstThird))
        (oneIs =>
          threeElim first second third other (connected network one other = True) (rewrite isSet at heldOther)
            (otherIs => rewrite oneIs, otherIs in back first second firstSecond)
            (otherIs => same second oneIs otherIs)
            (otherIs => rewrite oneIs, otherIs in pair second third secondThird))
        (oneIs =>
          threeElim first second third other (connected network one other = True) (rewrite isSet at heldOther)
            (otherIs => rewrite oneIs, otherIs in back first third firstThird)
            (otherIs => rewrite oneIs, otherIs in back second third secondThird)
            (otherIs => same third oneIs otherIs)))

-- A set of three is the set of its three computers, in order, and they
-- are different.
theorem threeListed (set: Set Computer) (three: set.size = 3) (goal: Prop)
    (found: (first: Computer) → (second: Computer) → (third: Computer) → set = Set.fromList [first, second, third] →
      Not (first = second) → Not (first = third) → Not (second = third) → goal):
    goal :=
  let distinct: List.Distinct set.toList := Map.keysDistinct set.items
  let sized: set.toList.length = 3 := rewrite <- Set.sizeToList set in three
  match keys: set.toList with
    | Nil => Void.exfalso (omega [sized])
    | Cons first Nil => Void.exfalso (omega [sized])
    | Cons first (Cons second Nil) => Void.exfalso (omega [sized])
    | Cons first (Cons second (Cons third (Cons fourth rest))) => Void.exfalso (omega [sized])
    | Cons first (Cons second (Cons third Nil)) =>
      let (Both firstOut (Both secondOut unused)) := distinct
      found first second third
        (Set.extIff set (Set.fromList [first, second, third]) (key => {
          forward = held => containsFromListOfMem key [first, second, third] (rewrite keys at ((Set.memToList set key).backward held: List.Mem key set.toList)),
          backward = held =>
            (Set.memToList set key).forward (rewrite keys in memOfContainsFromList key [first, second, third] held)
        }))
        (same => firstOut (Inl (Eq.sym same)))
        (same => firstOut (Inr (Inl (Eq.sym same))))
        (same => secondOut (Inl (Eq.sym same)))

-- The program's sets of three are the puzzle's.
theorem setsOfThreeIff (network: Network) (set: Set Computer):
    Iff ((setsOfThree network.links).contains set = True) (InterConnectedThree network set) := {
  forward = held =>
    let kept := Eq.trans (Eq.sym (Set.containsFilter (Set.fromList (madeSets network.links)) set (set => set.size == 3))) held
    let made := memOfContainsFromList set (madeSets network.links) (Bool.andLeft _ _ kept)
    Both (sizeThree set (Bool.andRight _ _ kept)) (madeConnected network set made),
  backward = (Both three connected) =>
    threeListed set three ((setsOfThree network.links).contains set = True)
      (first second third isSet firstSecond firstThird secondThird =>
        let inSet: (member: Computer) → List.Mem member [first, second, third] → set.contains member = True :=
          member listed => rewrite isSet in containsFromListOfMem member [first, second, third] listed
        let linked: (one: Computer) → (other: Computer) → List.Mem one [first, second, third] → List.Mem other [first, second, third] →
            Not (one = other) → (neighbours network.links one).contains other = True :=
          one other oneListed otherListed different =>
            (linkedIff network one other).backward (connected one other (inSet one oneListed) (inSet other otherListed) different)
        let firstListed: List.Mem first [first, second, third] := Inl rfl
        let secondListed: List.Mem second [first, second, third] := Inr (Inl rfl)
        let thirdListed: List.Mem third [first, second, third] := Inr (Inr (Inl rfl))
        let firstSecondLinked := linked first second firstListed secondListed firstSecond
        let firstThirdLinked := linked first third firstListed thirdListed firstThird
        let secondThirdLinked := linked second third secondListed thirdListed secondThird
        let firstKeyed := (Set.memToList network.links.keySet first).backward (hasLinksOfLinked network first second firstSecondLinked)
        let thirdCommon: List.Mem third (neighbours network.links second |> .intersect (neighbours network.links first) |> .toList) :=
          (Set.memToList (neighbours network.links second |> .intersect (neighbours network.links first)) third).backward
            (rewrite Set.containsIntersect (neighbours network.links second) third (neighbours network.links first), secondThirdLinked, firstThirdLinked in rfl)
        let made: List.Mem (Set.fromList [first, second, third]) (madeSets network.links) :=
          List.memFlatMapIntro (setsWith network.links) first (Set.fromList [first, second, third]) network.links.keySet.toList firstKeyed
            (List.memFlatMapIntro
              (second => neighbours network.links second |> .intersect (neighbours network.links first) |> .toList |> .map (third => Set.fromList [first, second, third]))
              second (Set.fromList [first, second, third]) (neighbours network.links first).toList
              ((Set.memToList (neighbours network.links first) second).backward firstSecondLinked)
              (List.memMap (neighbours network.links second |> .intersect (neighbours network.links first) |> .toList) third thirdCommon
                (third => Set.fromList [first, second, third])))
        rewrite Set.containsFilter (Set.fromList (madeSets network.links)) set (set => set.size == 3), three, isSet,
          containsFromListOfMem (Set.fromList [first, second, third]) (madeSets network.links) made
          in rfl)
}

-- "How many contain at least one computer with a name that starts with t?"
theorem part1Correct (network: Network): IsPart1 network (solvePart1 network) :=
  Witness ((setsOfThree network.links).filter mightBeChiefs)
    (Both
      (set => {
        forward = held =>
          let kept := Eq.trans (Eq.sym (Set.containsFilter (setsOfThree network.links) set mightBeChiefs)) held
          Both ((setsOfThreeIff network set).forward (Bool.andLeft _ _ kept)) (Bool.andRight _ _ kept),
        backward = (Both three withT) =>
          rewrite Set.containsFilter (setsOfThree network.links) set mightBeChiefs, (setsOfThreeIff network set).backward three in withT
      })
      rfl)
