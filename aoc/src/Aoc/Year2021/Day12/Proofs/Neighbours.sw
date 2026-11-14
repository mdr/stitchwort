--| The program's neighbour table: a cave's neighbours are the caves the
--| spec calls connected to it, each once.

namespace Aoc.Year2021.Day12.Proofs
import Aoc.Year2021.Day12 (..)
import Aoc.Year2021.Day12.Spec (..)
import Std (Bool, DecEq, Eq, Exists, Iff, List, Option, Void)

--| `==` is false between different things.
theorem differ ∀ (x y: Cave) (ne: x ≠ y): (x == y) = False := match e: x == y with
  | True => Void.exfalso (ne e.read)
  | False => rfl

--| Looking a cave up in a table built from a list of caves.
theorem lookupBuilt ∀ (f: Cave → List Cave) (cave: Cave) (cs: List Cave)
    (member: cave ∈ cs):
    List.lookup (cs.map (c => (c, f c))) cave = Some (f cave) :=
  match cs with
    | [c, ..rest] =>
      match e: c == cave with
        | True => rewrite e.read in rfl
        | False =>
          match member with
            | Inl same => Void.exfalso (Bool.trueNotFalse (rewrite same, DecEq.refl cave at e))
            | Inr later => lookupBuilt f cave rest later

theorem lookupMissing ∀ (f: Cave → List Cave) (cave: Cave) (cs: List Cave)
    (missing: ¬(cave ∈ cs)):
    List.lookup (cs.map (c => (c, f c))) cave = None :=
  match cs with
    | [] => rfl
    | [c, ..rest] =>
      match e: c == cave with
        | True => Void.exfalso (missing (Inl e.read))
        | False => lookupMissing f cave rest (later => missing (Inr later))

--| Both caves of a passage are named in one.
theorem endsNamed ∀ (passages: List Passage) (passage: Passage)
    (member: passage ∈ passages):
    passage.from ∈ caves passages ∧ passage.to ∈ caves passages :=
  Both
    ((List.memUnique passage.from _).backward
      (List.memFlatMapIntro (p => [p.from, p.to]) passage passage.from passages member (Inl rfl)))
    ((List.memUnique passage.to _).backward
      (List.memFlatMapIntro (p => [p.from, p.to]) passage passage.to passages member (Inr (Inl rfl))))

--| Both caves of a connection are named in a passage.
theorem connectedNamed ∀ (passages: List Passage) (a b: Cave)
    (h: connected passages a b = True):
    a ∈ caves passages ∧ b ∈ caves passages :=
  let Witness edge (Both member joins) := h
  match edge with
    | { from, to } =>
      let named := endsNamed passages { from, to } member
      match joins with
        | Inl (Both fromA toB) => rewrite <- fromA.read, <- toB.read in named
        | Inr (Both fromB toA) => rewrite <- fromB.read, <- toA.read in Both (And.right named) (And.left named)

--| The caves a passage leads to from `cave`, as the program finds them, are
--| those connected to it...
theorem neighboursOfMem ∀ (passages: List Passage) (cave y: Cave):
    y ∈ neighboursOf passages cave ↔ connected passages cave y = True :=
  {
    forward = found =>
      let leadsTo := passage => passage.leadsTo cave
      List.anyElim
        (edge => y ∈ leadsTo edge) _
        passages
        (List.memFlatMapElim leadsTo y passages ((List.memUnique y _).forward found))
        (edge member inEdge =>
          match edge with
            | { from, to } =>
              match fc: from == cave with
                | True =>
                  match inEdge with
                    | Inl same => Witness { from, to } (Both member (rewrite fc, <- same, DecEq.refl to in rfl))
                    | Inr nothing => Void.exfalso nothing
                | False =>
                  match tc: to == cave with
                    | True =>
                      match inEdge with
                        | Inl same =>
                          Witness { from, to } (Both member (rewrite fc, tc, <- same, DecEq.refl from in rfl))
                        | Inr nothing => Void.exfalso nothing),
    backward = joined =>
      let leadsTo := passage => passage.leadsTo cave
      let Witness edge (Both member joins) := joined
      match edge with
        | { from, to } =>
          let inEdge: y ∈ leadsTo { from, to } := match joins with
            | Inl (Both fromC toY) => rewrite fromC in Inl toY.read
            | Inr (Both fromY tc) =>
              match fc: from == cave with
                | True => Inl (Eq.trans tc.read (Eq.trans (Eq.sym fc.read) fromY.read))
                | False => rewrite tc in Inl fromY.read
          (List.memUnique y _).backward (List.memFlatMapIntro leadsTo { from, to } y passages member inEdge)
  }

--| ...and the table gives them.
theorem tableMem ∀ (passages: List Passage) (cave y: Cave):
    y ∈ lookupNeighbours (neighbourTable passages) cave ↔ connected passages cave y = True :=
  match named: (caves passages).contains cave with
    | True =>
      rewrite lookupBuilt (neighboursOf passages) cave (caves passages) named.read in neighboursOfMem passages cave y
    | False => {
      forward = found =>
        Void.exfalso
          (rewrite lookupMissing (neighboursOf passages) cave (caves passages) (member =>
            Bool.trueNotFalse (rewrite (List.memContains (caves passages) cave).backward member at named)) at found),
      backward = joined =>
        Void.exfalso
          (Bool.trueNotFalse
            (rewrite (List.memContains (caves passages) cave).backward
              (And.left (connectedNamed passages cave y joined)) at named))
    }

theorem tableDistinct ∀ (passages: List Passage) (cave: Cave):
    List.Distinct (lookupNeighbours (neighbourTable passages) cave) :=
  match named: (caves passages).contains cave with
    | True => rewrite lookupBuilt (neighboursOf passages) cave (caves passages) named.read in List.distinctUnique _
    | False =>
      rewrite lookupMissing (neighboursOf passages) cave (caves passages) (member =>
            Bool.trueNotFalse (rewrite (List.memContains (caves passages) cave).backward member at named)) in
        List.distinctNil [a := Cave]
