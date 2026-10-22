-- Day 7, part 2, proved for every manifold (`part2Correct`, at the bottom):
-- the program's count is the number of timelines in Proofs/Spec.sw. The
-- program works up from the bottom row, and each column's count is the
-- number of timelines of a particle falling into it (`countsAre`), by
-- induction on the rows: a column without a splitter has the timelines of
-- the column below, and a splitter's are those going left followed by those
-- going right, each tagged with the splitter (`countStep`).

namespace Aoc.Day07.Proofs
import Aoc.Day07 (..)
import Std (Eq, Fin, List, Nat, Option, Vec, Void)

-- `splitRow` column by column.
theorem splitRowAt (row: Vec Bool w) (below: Vec Nat w) (c: Nat):
    List.getOr 1 c (Vec.toList (splitRow row below))
      = (if splitterAt row c then List.getOr 1 c (Cons 1 (Vec.toList below)) + List.getOr 1 (Succ c) (Vec.toList below) else List.getOr 1 c (Vec.toList below)) :=
  let sides := Vec.zipWith (l r => l + r) (below.shiftRight 1) (below.shiftLeft 1)
  rewrite Vec.getOrZipWith3 (s here sides => if s then sides else here) False 1 2 1 rfl row below sides c in
    match e: splitterAt row c with
      | False => rfl
      | True  =>
        let inside: c < w := rewrite <- Vec.lengthToList row in setInside (Vec.toList row) c e
        rewrite Vec.getOrZipWith (l r => l + r) 1 1 2 rfl (below.shiftRight 1) (below.shiftLeft 1) c,
          Vec.getOrShiftLeft 1 below c, Vec.getOrShiftRight 1 1 below c inside

-- The counts below the rows `ls`, as `timelineCounts` works them out.
def countsBelow (w: Nat) (ls: List (Vec Bool w)): Vec Nat w := List.foldRight splitRow (Vec.replicate w 1) ls

-- One row up: a column's count from the counts below, against the
-- timelines from that column.
theorem countStep (l: Vec Bool w) (rest: List (Vec Bool w)) (r: Nat) (c: Nat) (below: List Nat)
    (ih: (c: Nat) -> List.getOr 1 c below = List.length (timelinesFrom (r + 1) c rest)):
    (if splitterAt l c then List.getOr 1 c (Cons 1 below) + List.getOr 1 (Succ c) below else List.getOr 1 c below)
      = List.length (timelinesFrom r c (Cons l rest)) :=
  match e: splitterAt l c with
    | True  =>
      match c with
        | Zero   => rewrite List.lengthMap _ _ in Eq.cong Succ (ih 1)
        | Succ b => rewrite List.lengthAppend _ _, List.lengthMap _ _, List.lengthMap _ _, Nat.addOne b, ih b, ih (Succ (Succ b))
    | False => ih c

-- Every column's count is the number of timelines from it.
theorem countsAre (w: Nat): (ls: List (Vec Bool w)) -> (r: Nat) -> (c: Nat) ->
    List.getOr 1 c (Vec.toList (countsBelow w ls)) = List.length (timelinesFrom r c ls)
  | Nil,         r, c => rewrite Vec.toListReplicate 1 w in List.getOrReplicate 1 c w
  | Cons l rest, r, c =>
    rewrite splitRowAt l (countsBelow w rest) c in
      countStep l rest r c (Vec.toList (countsBelow w rest)) (c => countsAre w rest (r + 1) c)

-- Part 2 is right: for every manifold, the printed answer is the number of
-- timelines of the particle from S.
theorem part2Correct (manifold: Manifold): solvePart2 manifold = part2Spec manifold :=
  rewrite <- Vec.getToList 1 (timelineCounts manifold) manifold.start in
    countsAre manifold.width manifold.rows 0 manifold.start.toNat
