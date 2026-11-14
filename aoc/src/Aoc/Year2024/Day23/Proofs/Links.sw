--| The program's links are the puzzle's connections: `other` is a neighbour
--| of `one` exactly when the map connects them (`linkedIff`), either way
--| round, and the computers with neighbours are the computers on the map
--| (`hasLinksIff`).

namespace Aoc.Year2024.Day23.Proofs
import Aoc.Year2024.Day23 (..)
import Aoc.Year2024.Day23.Spec (..)
import Std (And, Bool, DecEq, Eq, Exists, Iff, List, Map, Option, Or, Set, Void)

--| The connections, both ways round, that start at `one`, found by the key
--| test `Map.groupBy` uses.
def startingAt (network: Network) (one: Computer): List Connection :=
  network.bothWays.filter ((pair: Connection) => Map.Spec.sameKey one pair.one)

theorem neighboursGet ∀ (links: Links) (one: Computer): links.neighbours one = (links.get one).getOrElse Set.empty :=
  rfl

--| A computer's neighbours are the far ends of the connections starting at
--| it.
theorem neighboursStartingAt ∀ (network: Network) (one other: Computer):
    (network.links.neighbours one).contains other
      = ((startingAt network one).map Connection.other |> .any (x => Map.Spec.sameKey other x)) :=
  rewrite neighboursGet network.links one,
      Map.getMap (Map.groupBy network.bothWays Connection.one) one (pairs =>
        pairs.map Connection.other |> .toList |> Set.fromList),
      Map.getGroupBy Connection.one one network.bothWays in
    match network.bothWays.filter ((pair: Connection) => Map.Spec.sameKey one pair.one) with
      | [] => rfl
      | [first, ..rest] => Set.containsFromList other ([first, ..rest] |> .map Connection.other)

--| The program's neighbours are the connections both ways round.
theorem neighboursIff ∀ (network: Network) (one other: Computer):
    ((network.links.neighbours one).contains other = True) ↔ ({ one = one, other = other } ∈ network.bothWays) :=
  {
    forward = held =>
      let found: ((startingAt network one).map Connection.other).any (x => Map.Spec.sameKey other x) = True :=
        rewrite <- neighboursStartingAt network one other in held
      let Witness x (Both member same) := found
      List.anyElim
        (pair => Connection.other pair = x)
        ({ one = one, other = other } ∈ network.bothWays)
        (startingAt network one)
        (List.memMapAny (startingAt network one) Connection.other x member)
        (pair kept far =>
          match pair with
            | { one = start, other = end } =>
              let (Both inBoth starts) :=
                List.memFilter network.bothWays ((pair: Connection) => Map.Spec.sameKey one pair.one) kept
              rewrite Map.Spec.sameKeySound one start starts, Map.Spec.sameKeySound other x same, <- far in inBoth),
    backward = inBoth =>
      rewrite neighboursStartingAt network one other in
        Witness other
          (Both
            (List.memMap
              (startingAt network one)
              ({ one = one, other = other })
              (List.memFilterIntro network.bothWays
                ((pair: Connection) => Map.Spec.sameKey one pair.one)
                inBoth
                (sameKeyRefl one))
              Connection.other)
            (sameKeyRefl other))
  }

--| The connections both ways round are the map's, read either way.
theorem bothWaysIff ∀ (network: Network) (one other: Computer):
    ({ one = one, other = other } ∈ network.bothWays) ↔ (connected network one other = True) :=
  {
    forward = inBoth =>
      List.anyElim
        ((pair: Connection) => ({ one = one, other = other }) ∈ [pair, pair.reverse])
        (connected network one other = True)
        network.connections
        (List.memFlatMapElim
          ((pair: Connection) => [pair, pair.reverse])
          ({ one = one, other = other })
          network.connections
          inBoth)
        (pair listed made =>
          match pair with
            | { one = start, other = end } =>
              match made with
                | Inl same =>
                  Witness { one = one, other = other }
                    (Both (rewrite same at listed) (Inl (DecEq.refl ({ one = one, other = other }))))
                | Inr (Inl swapped) =>
                  Witness { one = other, other = one }
                    (Both
                      (rewrite Eq.cong Connection.other swapped, Eq.cong Connection.one swapped at listed)
                      (Inr (DecEq.refl ({ one = other, other = one }))))
                | Inr (Inr none) => Void.exfalso none),
    backward = joined =>
      let Witness pair (Both listed matches) := joined
      match matches with
        | Inl same =>
          List.memFlatMapIntro
            ((pair: Connection) => [pair, pair.reverse])
            ({ one = one, other = other })
            ({ one = one, other = other })
            network.connections
            (rewrite <- same.read in listed)
            (firstOfTwo ({ one = one, other = other }) ({ one = other, other = one }))
        | Inr swapped =>
          List.memFlatMapIntro
            ((pair: Connection) => [pair, pair.reverse])
            ({ one = other, other = one })
            ({ one = one, other = other })
            network.connections
            (rewrite <- swapped.read in listed)
            (secondOfTwo ({ one = other, other = one }) ({ one = one, other = other }))
  }

--| `other` is a neighbour of `one` exactly when the map connects them.
theorem linkedIff ∀ (network: Network) (one other: Computer):
    ((network.links.neighbours one).contains other = True) ↔ (connected network one other = True) :=
  {
    forward = held => (bothWaysIff network one other).forward ((neighboursIff network one other).forward held),
    backward = joined => (neighboursIff network one other).backward ((bothWaysIff network one other).backward joined)
  }

--| "Connections aren't directional".
theorem connectedSymmetric ∀ (network: Network) (one other: Computer)
    (joined: connected network one other = True):
    connected network other one = True :=
  let Witness pair (Both listed matches) := joined
  match matches with
    | Inl same => Witness pair (Both listed (Inr same))
    | Inr swapped => Witness pair (Both listed (Inl swapped))

theorem linkedSymmetric ∀ (network: Network) (one other: Computer)
    (held: (network.links.neighbours one).contains other = True):
    (network.links.neighbours other).contains one = True :=
  (linkedIff network other one).backward
    (connectedSymmetric network one other ((linkedIff network one other).forward held))

--| A computer in a connection is on the map.
theorem connectedComputer ∀ (network: Network) (one other: Computer)
    (joined: connected network one other = True):
    one ∈ computers network :=
  let Witness pair (Both listed matches) := joined
  match matches with
    | Inl same =>
      List.memFlatMapIntro
        ((pair: Connection) => [pair.one, pair.other])
        ({ one = one, other = other })
        one
        network.connections
        (rewrite <- same.read in listed)
        (firstOfTwo one other)
    | Inr swapped =>
      List.memFlatMapIntro
        ((pair: Connection) => [pair.one, pair.other])
        ({ one = other, other = one })
        one
        network.connections
        (rewrite <- swapped.read in listed)
        (secondOfTwo other one)

--| A computer on the map has a neighbour.
theorem computerConnected ∀ (network: Network) (computer: Computer)
    (onMap: computer ∈ computers network):
    Exists Computer (other => connected network computer other = True) :=
  List.anyElim
    ((pair: Connection) => computer ∈ [pair.one, pair.other])
    (Exists Computer (other => connected network computer other = True))
    network.connections
    (List.memFlatMapElim ((pair: Connection) => [pair.one, pair.other]) computer network.connections onMap)
    (pair listed named =>
      match pair with
        | { one = start, other = end } =>
          match named with
            | Inl first =>
              Witness end
                (Witness { one = start, other = end }
                  (Both listed (Inl (rewrite first in DecEq.refl ({ one = computer, other = end })))))
            | Inr (Inl second) =>
              Witness start
                (Witness { one = start, other = end }
                  (Both listed (Inr (rewrite second in DecEq.refl ({ one = start, other = computer })))))
            | Inr (Inr none) => Void.exfalso none)

--| A computer with a neighbour has an entry in the links.
theorem hasLinksOfLinked ∀ (network: Network) (one other: Computer)
    (held: (network.links.neighbours one).contains other = True):
    network.links.keySet.contains one = True :=
  rewrite Map.containsKeySet network.links one in match found: Map.get network.links one with | Some set => rfl

--| The computers with links are the computers on the map.
theorem hasLinksIff ∀ (network: Network) (computer: Computer):
    (network.links.keySet.contains computer = True) ↔ (computer ∈ computers network) :=
  {
    forward = keyed =>
      match found: Map.get network.links computer with
        | None => Void.exfalso (Bool.falseNotTrue (rewrite Map.containsKeySet network.links computer, found at keyed))
        | Some set =>
          List.anyTrueElim
            (startingAt network computer)
            (pair => True)
            (computer ∈ computers network)
            (match starting: network.bothWays.filter ((pair: Connection) => Map.Spec.sameKey computer pair.one) with
              | [] =>
                Void.exfalso
                  (Option.noneNotSome set
                    (rewrite Map.getMap (Map.groupBy network.bothWays Connection.one) computer (pairs =>
                      pairs.map Connection.other |> .toList |> Set.fromList), Map.getGroupBy Connection.one computer
                        network.bothWays, starting at found))
              | [first, ..rest] => rfl)
            (pair kept unused =>
              match pair with
                | { one = start, other = end } =>
                  let (Both inBoth starts) :=
                    List.memFilter network.bothWays ((pair: Connection) => Map.Spec.sameKey computer pair.one) kept
                  connectedComputer network computer end
                    ((bothWaysIff network computer end).forward
                      (rewrite <- Map.Spec.sameKeySound computer start starts at inBoth))),
    backward = onMap =>
      Exists.elim (computerConnected network computer onMap) (other joined =>
        hasLinksOfLinked network computer other ((linkedIff network computer other).backward joined))
  }
