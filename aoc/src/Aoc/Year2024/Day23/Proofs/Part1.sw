--| Part 1: the program's sets of three are the puzzle's (`setsOfThreeIff`),
--| so it counts the sets of three inter-connected computers with a t name,
--| for every network (`part1Correct`).
--
-- A set the program makes is a computer, a neighbour and a neighbour of
-- both, so each is connected to the other two; it keeps those of size 3.
-- Back the other way, a set of size 3 lists as three different computers,
-- the first of which has links; the program makes that set from them.

namespace Aoc.Year2024.Day23.Proofs
import Aoc.Year2024.Day23 (..)
import Aoc.Year2024.Day23.Spec (..)
import Std (And, Bool, DecEq, Eq, Exists, Iff, List, Map, Nat, Not, Or, Set, Void)

theorem sizeThree ∀ (set: Set Computer) (three: (set.size == 3) = True): set.size = 3 := three.read

--| What the program makes before keeping the sets of three: the sets from
--| each computer with links.
def madeSets (links: Links): List Party := links.keySet.toList.flatMap links.setsWith

--| A set the program makes is three computers, each pair neighbours.
theorem madeElim ∀ (network: Network) (party: Party) (made: List.Mem party (madeSets network.links)) (goal: Prop)
    (found: ∀ (first second third: Computer) => party.members = Set.fromList [first, second, third] →
      (network.links.neighbours first).contains second = True → (network.links.neighbours first).contains third = True →
      (network.links.neighbours second).contains third = True → goal):
    goal :=
  List.anyElim (first => List.Mem party (network.links.setsWith first)) goal network.links.keySet.toList
    (List.memFlatMapElim network.links.setsWith party network.links.keySet.toList made)
    (first unused fromFirst =>
      let firstNeighbours := network.links.neighbours first
      List.anyElim
        (second => List.Mem party (network.links.neighbours second |> .intersect firstNeighbours |> .toList |> .map (third => ({ members = Set.fromList [first, second, third] }))))
        goal firstNeighbours.toList
        (List.memFlatMapElim
          (second => network.links.neighbours second |> .intersect firstNeighbours |> .toList |> .map (third => ({ members = Set.fromList [first, second, third] })))
          party firstNeighbours.toList fromFirst)
        (second secondListed fromSecond =>
          List.anyElim (third => ({ members = Set.fromList [first, second, third] }) = party) goal (network.links.neighbours second |> .intersect firstNeighbours |> .toList)
            (List.memMapAny (network.links.neighbours second |> .intersect firstNeighbours |> .toList) (third => ({ members = Set.fromList [first, second, third] })) party fromSecond)
            (third thirdListed isSet =>
              let (Both secondThird firstThird) :=
                intersectElim (network.links.neighbours second) firstNeighbours third
                  ((Set.memToList (network.links.neighbours second |> .intersect firstNeighbours) third).forward thirdListed)
              found first second third (Eq.cong Party.members (Eq.sym isSet)) ((Set.memToList firstNeighbours second).forward secondListed) firstThird secondThird)))

--| The sets the program makes are all connected.
theorem madeConnected ∀ (network: Network) (party: Party) (made: List.Mem party (madeSets network.links)): AllConnected network party :=
  madeElim network party made (AllConnected network party)
    (first second third isSet firstSecond firstThird secondThird one other heldOne heldOther different =>
      let pair: ∀ (one other: Computer) => (network.links.neighbours one).contains other = True → connected network one other = True :=
        one other held => (linkedIff network one other).forward held
      let back: ∀ (one other: Computer) => (network.links.neighbours one).contains other = True → connected network other one = True :=
        one other held => (linkedIff network other one).forward (linkedSymmetric network one other held)
      let same: ∀ (member: Computer) => one = member → other = member → connected network one other = True :=
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

--| A set of three is the set of its three computers, in order, and they
--| are different.
theorem threeListed ∀ (set: Set Computer) (three: set.size = 3) (goal: Prop)
    (found: ∀ (first second third: Computer) => set = Set.fromList [first, second, third] →
      first ≠ second → first ≠ third → second ≠ third → goal):
    goal :=
  let distinct: List.Distinct set.toList := Map.keysDistinct set.items
  let sized: set.toList.length = 3 := rewrite <- Set.sizeToList set in three
  match keys: set.toList with
    | [] => Void.exfalso (omega [sized])
    | [first] => Void.exfalso (omega [sized])
    | [first, second] => Void.exfalso (omega [sized])
    | [first, second, third, fourth, ..rest] => Void.exfalso (omega [sized])
    | [first, second, third] =>
      let (Both firstOut (Both secondOut unused)) := distinct
      found first second third
        (Set.extIff set (Set.fromList [first, second, third]) (key => {
          forward = held => (Set.containsFromListIff [first, second, third] key).backward (rewrite keys at held.read),
          backward = held =>
            (Set.memToList set key).forward (rewrite keys in (Set.containsFromListIff [first, second, third] key).forward held)
        }))
        (same => firstOut (Inl (Eq.sym same)))
        (same => firstOut (Inr (Inl (Eq.sym same))))
        (same => secondOut (Inl (Eq.sym same)))

--| The program's sets of three are the puzzle's.
theorem setsOfThreeIff ∀ (network: Network) (party: Party):
    (network.links.setsOfThree.contains party = True) ↔ (InterConnectedThree network party) := {
  forward = held =>
    let kept := Eq.trans (Eq.sym (Set.containsFilter (Set.fromList (madeSets network.links)) party (party => party.size == 3))) held
    let (Both inMade sized) := kept
    Both (sizeThree party.members sized) (madeConnected network party ((Set.memToListFromList (madeSets network.links) party).forward inMade.read)),
  backward = (Both three connected) =>
    threeListed party.members three (network.links.setsOfThree.contains party = True)
      (first second third isSet firstSecond firstThird secondThird =>
        let inSet: ∀ (member: Computer) => List.Mem member [first, second, third] → party.members.contains member = True :=
          member listed => rewrite isSet in (Set.containsFromListIff [first, second, third] member).backward listed
        let linked: ∀ (one other: Computer) => List.Mem one [first, second, third] → List.Mem other [first, second, third] →
            one ≠ other → (network.links.neighbours one).contains other = True :=
          one other oneListed otherListed different =>
            (linkedIff network one other).backward (connected one other (inSet one oneListed) (inSet other otherListed) different)
        let firstListed: List.Mem first [first, second, third] := Inl rfl
        let secondListed: List.Mem second [first, second, third] := Inr (Inl rfl)
        let thirdListed: List.Mem third [first, second, third] := Inr (Inr (Inl rfl))
        let firstSecondLinked := linked first second firstListed secondListed firstSecond
        let firstThirdLinked := linked first third firstListed thirdListed firstThird
        let secondThirdLinked := linked second third secondListed thirdListed secondThird
        let firstKeyed := (Set.memToList network.links.keySet first).backward (hasLinksOfLinked network first second firstSecondLinked)
        let thirdCommon: List.Mem third (network.links.neighbours second |> .intersect (network.links.neighbours first) |> .toList) :=
          (Set.memToList (network.links.neighbours second |> .intersect (network.links.neighbours first)) third).backward
            (rewrite Set.containsIntersect (network.links.neighbours second) third (network.links.neighbours first), secondThirdLinked, firstThirdLinked in rfl)
        let made: List.Mem ({ members = Set.fromList [first, second, third] }) (madeSets network.links) :=
          List.memFlatMapIntro network.links.setsWith first ({ members = Set.fromList [first, second, third] }) network.links.keySet.toList firstKeyed
            (List.memFlatMapIntro
              (second => network.links.neighbours second |> .intersect (network.links.neighbours first) |> .toList |> .map (third => ({ members = Set.fromList [first, second, third] })))
              second ({ members = Set.fromList [first, second, third] }) (network.links.neighbours first).toList
              ((Set.memToList (network.links.neighbours first) second).backward firstSecondLinked)
              (List.memMap (network.links.neighbours second |> .intersect (network.links.neighbours first) |> .toList) third thirdCommon
                (third => ({ members = Set.fromList [first, second, third] }))))
        let isParty: party = ({ members = Set.fromList [first, second, third] }) := Party.ext party ({ members = Set.fromList [first, second, third] }) isSet
        let sizeKept: (party.members.size == 3) = True := rewrite three in rfl
        rewrite Set.containsFilter (Set.fromList (madeSets network.links)) party (party => party.size == 3), sizeKept, isParty,
          (Set.containsFromListIff (madeSets network.links) ({ members = Set.fromList [first, second, third] })).backward made
          in rfl)
}

--| "How many contain at least one computer with a name that starts with t?"
theorem part1Correct ∀ (network: Network): IsPart1 network (solvePart1 network) :=
  Witness (network.links.setsOfThree.filter Party.mightHaveChief)
    (Both
      (party => {
        forward = held =>
          let kept := Eq.trans (Eq.sym (Set.containsFilter network.links.setsOfThree party Party.mightHaveChief)) held
          Both ((setsOfThreeIff network party).forward kept.left) kept.right,
        backward = (Both three withT) =>
          rewrite Set.containsFilter network.links.setsOfThree party Party.mightHaveChief, (setsOfThreeIff network party).backward three in withT
      })
      rfl)
