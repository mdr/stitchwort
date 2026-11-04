--| The program's neighbour table: a cave's neighbours are the caves the
--| spec calls connected to it, each once.

namespace Aoc.Year2021.Day12.Proofs
import Aoc.Year2021.Day12 (..)
import Aoc.Year2021.Day12.Spec (connected)
import Std (Bool, DecEq, Eq, Exists, Iff, List, Option, Void)

--| `==` is false between different things.
theorem differ (x: Text) (y: Text) (ne: x ≠ y): (x == y) = False :=
  match e: x == y with
    | True => Void.exfalso (ne (DecEq.sound x y e))
    | False => rfl

--| Looking a cave up in a table built from a list of caves.
theorem lookupBuilt (f: Text → List Text) (cave: Text): (cs: List Text) → cave ∈ cs → List.lookup (cs.map (c => (c, f c))) cave = Some (f cave)
  | Nil, member => Void.exfalso member
  | Cons c rest, member =>
    match e: c == cave with
      | True => rewrite DecEq.sound c cave e in rfl
      | False =>
        match member with
          | Inl same => Void.exfalso (Bool.trueNotFalse (rewrite same, DecEq.refl cave at e))
          | Inr later => lookupBuilt f cave rest later

theorem lookupMissing (f: Text → List Text) (cave: Text): (cs: List Text) → ¬(cave ∈ cs) → List.lookup (cs.map (c => (c, f c))) cave = None
  | Nil, missing => rfl
  | Cons c rest, missing =>
    match e: c == cave with
      | True => Void.exfalso (missing (Inl (DecEq.sound c cave e)))
      | False => lookupMissing f cave rest (later => missing (Inr later))

--| Both caves of a passage are named in one.
theorem endsNamed (passages: List (Text, Text)) (from: Text) (to: Text) (member: (from, to) ∈ passages):
    from ∈ caves passages ∧ to ∈ caves passages :=
  Both
    ((List.memDistinct from _).backward (List.memFlatMapIntro (((a, b)) => [a, b]) (from, to) from passages member (Inl rfl)))
    ((List.memDistinct to _).backward (List.memFlatMapIntro (((a, b)) => [a, b]) (from, to) to passages member (Inr (Inl rfl))))

--| Both caves of a connection are named in a passage.
theorem connectedNamed (passages: List (Text, Text)) (a: Text) (b: Text) (h: connected passages a b = True):
    a ∈ caves passages ∧ b ∈ caves passages :=
  List.anyTrueElim passages (((from, to)) => (from == a && to == b) || (from == b && to == a)) _ h (edge member joins =>
    match edge with
      | (from, to) =>
        let named := endsNamed passages from to member
        Bool.orElim (from == a && to == b) (from == b && to == a) _ joins
          (forward =>
            rewrite <- DecEq.sound from a (Bool.andLeft _ _ forward), <- DecEq.sound to b (Bool.andRight _ _ forward) in named)
          (backward =>
            rewrite <- DecEq.sound from b (Bool.andLeft _ _ backward), <- DecEq.sound to a (Bool.andRight _ _ backward) in
              Both (And.right named) (And.left named)))

--| The caves a passage leads to from `cave`, as the program finds them, are
--| those connected to it...
theorem neighboursOfMem (passages: List (Text, Text)) (cave: Text) (y: Text): y ∈ neighboursOf passages cave ↔ connected passages cave y = True := {
  forward = found =>
    let leadsTo := ((from, to)) => if from == cave then [to] else if to == cave then [from] else []
    List.anyElim (edge => y ∈ leadsTo edge) _ passages (List.memFlatMapElim leadsTo y passages ((List.memDistinct y _).forward found)) (edge member inEdge =>
      match edge with
        | (from, to) =>
          match fc: from == cave with
            | True =>
              match inEdge with
                | Inl same => List.anyOfMem passages _ (from, to) (rewrite fc, <- same, DecEq.refl to in rfl) member
                | Inr nothing => Void.exfalso nothing
            | False =>
              match tc: to == cave with
                | True =>
                  match inEdge with
                    | Inl same => List.anyOfMem passages _ (from, to) (rewrite fc, tc, <- same, DecEq.refl from in rfl) member
                    | Inr nothing => Void.exfalso nothing
                | False => Void.exfalso inEdge),
  backward = joined =>
    let leadsTo := ((from, to)) => if from == cave then [to] else if to == cave then [from] else []
    List.anyTrueElim passages (((from, to)) => (from == cave && to == y) || (from == y && to == cave)) _ joined (edge member joins =>
      match edge with
        | (from, to) =>
          let inEdge: y ∈ leadsTo (from, to) :=
            Bool.orElim (from == cave && to == y) (from == y && to == cave) _ joins
              (forward => rewrite Bool.andLeft _ _ forward in Inl (DecEq.sound to y (Bool.andRight _ _ forward)))
              (backward =>
                let fy := DecEq.sound from y (Bool.andLeft _ _ backward)
                let tc := Bool.andRight _ _ backward
                match fc: from == cave with
                  | True => Inl (Eq.trans (DecEq.sound to cave tc) (Eq.trans (Eq.sym (DecEq.sound from cave fc)) fy))
                  | False => rewrite tc in Inl fy)
          (List.memDistinct y _).backward (List.memFlatMapIntro leadsTo (from, to) y passages member inEdge))
}

--| ...and the table gives them.
theorem tableMem (passages: List (Text, Text)) (cave: Text) (y: Text):
    y ∈ lookupNeighbours (neighbourTable passages) cave ↔ connected passages cave y = True :=
  match named: (caves passages).contains cave with
    | True =>
      rewrite lookupBuilt (neighboursOf passages) cave (caves passages) ((List.memContains (caves passages) cave).forward named) in
        neighboursOfMem passages cave y
    | False => {
      forward = found => Void.exfalso (rewrite lookupMissing (neighboursOf passages) cave (caves passages) (member => Bool.trueNotFalse (rewrite (List.memContains (caves passages) cave).backward member at named)) at found),
      backward = joined => Void.exfalso (Bool.trueNotFalse (rewrite (List.memContains (caves passages) cave).backward (And.left (connectedNamed passages cave y joined)) at named))
    }

theorem tableDistinct (passages: List (Text, Text)) (cave: Text): List.Distinct (lookupNeighbours (neighbourTable passages) cave) :=
  match named: (caves passages).contains cave with
    | True =>
      rewrite lookupBuilt (neighboursOf passages) cave (caves passages) ((List.memContains (caves passages) cave).forward named) in
        List.distinctNoRepeats _
    | False =>
      rewrite lookupMissing (neighboursOf passages) cave (caves passages) (member => Bool.trueNotFalse (rewrite (List.memContains (caves passages) cave).backward member at named)) in
        List.distinctNil [a := Text]
