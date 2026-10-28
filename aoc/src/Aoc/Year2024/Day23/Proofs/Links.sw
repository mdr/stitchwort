-- The program's links are the puzzle's connections: `other` is a neighbour
-- of `one` exactly when the map connects them (`linkedIff`), either way
-- round, and the computers with neighbours are the computers on the map
-- (`hasLinksIff`).

namespace Aoc.Year2024.Day23.Proofs
import Aoc.Year2024.Day23 (..)
import Aoc.Year2024.Day23.Spec (..)
import Std (And, Bool, DecEq, Eq, Exists, Iff, List, Map, Option, Or, Pair, Set, Void)

-- The connections, both ways round, that start at `one`, found by the key
-- test `Map.groupBy` uses.
def startingAt (network: Network) (one: Computer): List (Computer, Computer) :=
  network.bothWays.filter ((pair: (Computer, Computer)) => Map.Spec.sameKey one pair.fst)

theorem neighboursGet (links: Links) (one: Computer): neighbours links one = (Map.get links one).getOrElse Set.empty := rfl

-- A computer's neighbours are the far ends of the connections starting at
-- it.
theorem neighboursStartingAt (network: Network) (one: Computer) (other: Computer):
    (neighbours network.links one).contains other = ((startingAt network one).map Pair.snd |> .any (x => Map.Spec.sameKey other x)) :=
  rewrite neighboursGet network.links one,
    Map.getMap (Map.groupBy network.bothWays Pair.fst) one (pairs => pairs.map Pair.snd |> Set.fromList),
    Map.getGroupBy Pair.fst one network.bothWays
    in
  match network.bothWays.filter ((pair: (Computer, Computer)) => Map.Spec.sameKey one pair.fst) with
    | Nil => rfl
    | Cons first rest => Set.containsFromList other (Cons first rest |> .map Pair.snd)

-- The program's neighbours are the connections both ways round.
theorem neighboursIff (network: Network) (one: Computer) (other: Computer):
    Iff ((neighbours network.links one).contains other = True) ((one, other) ∈ network.bothWays) := {
  forward = held =>
    List.anyTrueElim ((startingAt network one).map Pair.snd) (x => Map.Spec.sameKey other x) ((one, other) ∈ network.bothWays)
      (rewrite <- neighboursStartingAt network one other in held)
      (x member same =>
        List.anyElim (pair => Pair.snd pair = x) ((one, other) ∈ network.bothWays) (startingAt network one)
          (List.memMapAny (startingAt network one) Pair.snd x member)
          (pair kept far =>
            match pair with
              | (start, end) =>
                let (Both inBoth starts) := List.memFilter network.bothWays ((pair: (Computer, Computer)) => Map.Spec.sameKey one pair.fst) (start, end) kept
                rewrite Map.Spec.sameKeySound one start starts, Map.Spec.sameKeySound other x same, <- far in inBoth)),
  backward = inBoth =>
    rewrite neighboursStartingAt network one other in
      List.anyOfMem ((startingAt network one).map Pair.snd) (x => Map.Spec.sameKey other x) other (sameKeyRefl other)
        (List.memMap (startingAt network one) (one, other)
          (List.memFilterIntro network.bothWays ((pair: (Computer, Computer)) => Map.Spec.sameKey one pair.fst) (one, other) inBoth (sameKeyRefl one)) Pair.snd)
}

-- The connections both ways round are the map's, read either way.
theorem bothWaysIff (network: Network) (one: Computer) (other: Computer):
    Iff ((one, other) ∈ network.bothWays) (connected network one other = True) := {
  forward = inBoth =>
    List.anyElim ((pair: (Computer, Computer)) => (one, other) ∈ [pair, (pair.snd, pair.fst)]) (connected network one other = True) network.connections
      (List.memFlatMapElim ((pair: (Computer, Computer)) => [pair, (pair.snd, pair.fst)]) (one, other) network.connections inBoth)
      (pair listed made =>
        match pair with
          | (start, end) =>
            match made with
              | Inl same =>
                List.anyOfMem network.connections (pair => pair == (one, other) || pair == (other, one)) (one, other)
                  (Bool.orLeft _ _ (DecEq.refl (one, other))) (rewrite same at listed)
              | Inr (Inl swapped) =>
                List.anyOfMem network.connections (pair => pair == (one, other) || pair == (other, one)) (other, one)
                  (Bool.orRight _ _ (DecEq.refl (other, one))) (rewrite Eq.cong Pair.snd swapped, Eq.cong Pair.fst swapped at listed)
              | Inr (Inr none) => Void.exfalso none),
  backward = joined =>
    List.anyTrueElim network.connections (pair => pair == (one, other) || pair == (other, one)) ((one, other) ∈ network.bothWays) joined
      (pair listed matches =>
        Bool.orElim (pair == (one, other)) (pair == (other, one)) ((one, other) ∈ network.bothWays) matches
          (same =>
            List.memFlatMapIntro ((pair: (Computer, Computer)) => [pair, (pair.snd, pair.fst)]) (one, other) (one, other) network.connections
              (rewrite <- DecEq.sound pair (one, other) same in listed) (firstOfTwo (one, other) (other, one)))
          (swapped =>
            List.memFlatMapIntro ((pair: (Computer, Computer)) => [pair, (pair.snd, pair.fst)]) (other, one) (one, other) network.connections
              (rewrite <- DecEq.sound pair (other, one) swapped in listed) (secondOfTwo (other, one) (one, other))))
}

-- `other` is a neighbour of `one` exactly when the map connects them.
theorem linkedIff (network: Network) (one: Computer) (other: Computer):
    Iff ((neighbours network.links one).contains other = True) (connected network one other = True) := {
  forward = held => (bothWaysIff network one other).forward ((neighboursIff network one other).forward held),
  backward = joined => (neighboursIff network one other).backward ((bothWaysIff network one other).backward joined)
}

-- "Connections aren't directional".
theorem connectedSymmetric (network: Network) (one: Computer) (other: Computer) (joined: connected network one other = True):
    connected network other one = True :=
  List.anyTrueElim network.connections (pair => pair == (one, other) || pair == (other, one)) (connected network other one = True) joined
    (pair listed matches =>
      List.anyOfMem network.connections (pair => pair == (other, one) || pair == (one, other)) pair
        (rewrite Bool.orComm (pair == (other, one)) (pair == (one, other)) in matches) listed)

theorem linkedSymmetric (network: Network) (one: Computer) (other: Computer) (held: (neighbours network.links one).contains other = True):
    (neighbours network.links other).contains one = True :=
  (linkedIff network other one).backward (connectedSymmetric network one other ((linkedIff network one other).forward held))

-- A computer in a connection is on the map.
theorem connectedComputer (network: Network) (one: Computer) (other: Computer) (joined: connected network one other = True):
    one ∈ computers network :=
  List.anyTrueElim network.connections (pair => pair == (one, other) || pair == (other, one)) (one ∈ computers network) joined
    (pair listed matches =>
      Bool.orElim (pair == (one, other)) (pair == (other, one)) (one ∈ computers network) matches
        (same =>
          List.memFlatMapIntro ((pair: (Computer, Computer)) => [pair.fst, pair.snd]) (one, other) one network.connections
            (rewrite <- DecEq.sound pair (one, other) same in listed) (firstOfTwo one other))
        (swapped =>
          List.memFlatMapIntro ((pair: (Computer, Computer)) => [pair.fst, pair.snd]) (other, one) one network.connections
            (rewrite <- DecEq.sound pair (other, one) swapped in listed) (secondOfTwo other one)))

-- A computer on the map has a neighbour.
theorem computerConnected (network: Network) (computer: Computer) (onMap: computer ∈ computers network):
    Exists Computer (other => connected network computer other = True) :=
  List.anyElim ((pair: (Computer, Computer)) => computer ∈ [pair.fst, pair.snd]) (Exists Computer (other => connected network computer other = True)) network.connections
    (List.memFlatMapElim ((pair: (Computer, Computer)) => [pair.fst, pair.snd]) computer network.connections onMap)
    (pair listed named =>
      match pair with
        | (start, end) =>
          match named with
            | Inl first =>
              Witness end
                (List.anyOfMem network.connections (pair => pair == (computer, end) || pair == (end, computer)) (start, end)
                  (rewrite first in Bool.orLeft _ _ (DecEq.refl (computer, end))) listed)
            | Inr (Inl second) =>
              Witness start
                (List.anyOfMem network.connections (pair => pair == (computer, start) || pair == (start, computer)) (start, end)
                  (rewrite second in Bool.orRight _ _ (DecEq.refl (start, computer))) listed)
            | Inr (Inr none) => Void.exfalso none)

-- A computer with a neighbour has an entry in the links.
theorem hasLinksOfLinked (network: Network) (one: Computer) (other: Computer) (held: (neighbours network.links one).contains other = True):
    network.links.keySet.contains one = True :=
  rewrite Map.containsKeySet network.links one in
  match found: Map.get network.links one with
    | Some set => rfl
    | None => Void.exfalso (Bool.falseNotTrue held)

-- The computers with links are the computers on the map.
theorem hasLinksIff (network: Network) (computer: Computer):
    Iff (network.links.keySet.contains computer = True) (computer ∈ computers network) := {
  forward = keyed =>
    match found: Map.get network.links computer with
      | None => Void.exfalso (Bool.falseNotTrue (rewrite Map.containsKeySet network.links computer, found at keyed))
      | Some set =>
        List.anyTrueElim (startingAt network computer) (pair => True) (computer ∈ computers network)
          (match starting: network.bothWays.filter ((pair: (Computer, Computer)) => Map.Spec.sameKey computer pair.fst) with
            | Nil =>
              Void.exfalso
                (Option.noneNotSome set
                  (rewrite Map.getMap (Map.groupBy network.bothWays Pair.fst) computer (pairs => pairs.map Pair.snd |> Set.fromList),
                    Map.getGroupBy Pair.fst computer network.bothWays, starting
                    at found))
            | Cons first rest => rfl)
          (pair kept unused =>
            match pair with
              | (start, end) =>
                let (Both inBoth starts) := List.memFilter network.bothWays ((pair: (Computer, Computer)) => Map.Spec.sameKey computer pair.fst) (start, end) kept
                connectedComputer network computer end
                  ((bothWaysIff network computer end).forward (rewrite <- Map.Spec.sameKeySound computer start starts at inBoth))),
  backward = onMap =>
    Exists.elim (computerConnected network computer onMap) (other joined => hasLinksOfLinked network computer other ((linkedIff network computer other).backward joined))
}
