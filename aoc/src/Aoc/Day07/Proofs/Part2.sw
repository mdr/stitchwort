-- Day 7, part 2, proved for every manifold (`part2Correct`, at the bottom):
-- the program's count is the number of timelines in Spec/Spec.sw. The
-- program works up from the bottom row, and each column's count is the
-- number of timelines of a particle falling into it (`countsAre`), by
-- induction on the rows: a column without a splitter has the timelines of
-- the column below, and a splitter's are those going left followed by those
-- going right, each tagged with the splitter (`countStep`).

namespace Aoc.Day07.Proofs
import Aoc.Day07 (..)
import Aoc.Day07.Spec (..)
import Std (Eq, Fin, List, Nat, Option, Vec, Void)

-- `splitRow` column by column.
theorem splitRowAt (row: Vec Bool w) (below: Vec Nat w) (c: Nat):
    Vec.getOr (splitRow row below) 1 c
      = (if splitterAt row c then Vec.getOr (VCons 1 below) 1 c + Vec.getOr below 1 (Succ c) else Vec.getOr below 1 c) :=
  let sides := below.around 1 (l _ r => l + r)
  rewrite Vec.getOrZipWith3 (s here sides => if s then sides else here) False 1 2 1 rfl row below sides c in
    match e: splitterAt row c with
      | False => rfl
      | True => Vec.getOrAround below 2 1 c (setInside row c e) (l _ r => l + r)

-- The counts below the rows `ls`, as `timelineCounts` works them out.
def countsBelow (w: Nat) (ls: List (Vec Bool w)): Vec Nat w := List.foldRight ls (Vec.replicate w 1) splitRow

-- One row up: a column's count from the counts below, against the
-- timelines from that column.
theorem countStep (l: Vec Bool w) (rest: List (Vec Bool w)) (r: Nat) (c: Nat) (below: Vec Nat w)
    (ih: (c: Nat) -> Vec.getOr below 1 c = List.length (timelinesFrom (r + 1) c rest)):
    (if splitterAt l c then Vec.getOr (VCons 1 below) 1 c + Vec.getOr below 1 (Succ c) else Vec.getOr below 1 c)
      = List.length (timelinesFrom r c (Cons l rest)) :=
  match e: splitterAt l c with
    | True =>
      match c with
        | Zero => rewrite List.lengthMap _ _ in Eq.cong Succ (ih 1)
        | Succ b => rewrite List.lengthAppend _ _, List.lengthMap _ _, List.lengthMap _ _, Nat.addOne b, ih b, ih (Succ (Succ b))
    | False => ih c

-- Every column's count is the number of timelines from it.
theorem countsAre (w: Nat): (ls: List (Vec Bool w)) -> (r: Nat) -> (c: Nat) ->
    Vec.getOr (countsBelow w ls) 1 c = List.length (timelinesFrom r c ls)
  | Nil, r, c => Vec.getOrReplicate 1 w c
  | Cons l rest, r, c =>
    rewrite List.foldRightCons rest l (Vec.replicate w 1) splitRow, splitRowAt l (countsBelow w rest) c in
      countStep l rest r c (countsBelow w rest) (c => countsAre w rest (r + 1) c)

-- Part 2 is right: for every manifold, the printed answer is the number of
-- timelines of the particle from S.
theorem part2Correct (manifold: Manifold): solvePart2 manifold = part2Spec manifold :=
  rewrite <- Vec.getOrGet (timelineCounts manifold) 1 manifold.start in
    countsAre manifold.width manifold.rows 0 manifold.start.toNat
