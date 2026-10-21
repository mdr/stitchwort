-- Day 7, part 2, proved for every input (`part2Correct`, at the bottom): the
-- program's count is the number of timelines in Proofs/Spec.sw. The
-- program works up from the bottom row, and each column's count is the
-- number of timelines of a particle falling into it (`countsAre`), by
-- induction on the rows: a column without a splitter has the timelines of
-- the column below, and a splitter's are those going left followed by those
-- going right, each tagged with the splitter (`countStep`).

namespace Aoc.Day07.Proofs
import Aoc.Day07 (..)
import Std (Eq)

-- `splitRow` column by column.
theorem splitRowAt (left: Nat): (flags: List Bool) -> (below: List Nat) -> List.length flags = List.length below -> (c: Nat) ->
    List.getOr 1 c (splitRow left flags below)
      = (if List.getOr False c flags then List.getOr 1 c (Cons left below) + List.getOr 1 (Succ c) below else List.getOr 1 c below)
  | Nil,       Nil,            e, c      => rfl
  | Nil,       Cons here rest, e, c      => Void.exfalso (Nat.zeroNotSucc (List.length rest) e)
  | Cons s ss, Nil,            e, c      => Void.exfalso (Nat.succNotZero (List.length ss) e)
  | Cons s ss, Cons here rest, e, Zero   => rewrite List.headOrGetOr 1 rest
  | Cons s ss, Cons here rest, e, Succ c => splitRowAt here ss rest (Nat.succInjective (List.length ss) (List.length rest) e) c

theorem splitRowLength (left: Nat): (flags: List Bool) -> (below: List Nat) -> List.length flags = List.length below ->
    List.length (splitRow left flags below) = List.length below
  | Nil,       Nil,            e => rfl
  | Nil,       Cons here rest, e => Void.exfalso (Nat.zeroNotSucc (List.length rest) e)
  | Cons s ss, Nil,            e => Void.exfalso (Nat.succNotZero (List.length ss) e)
  | Cons s ss, Cons here rest, e => Eq.cong Succ (splitRowLength here ss rest (Nat.succInjective (List.length ss) (List.length rest) e))

-- The counts below the rows `ls`, as `timelineCounts` works them out.
def countsBelow (w: Nat) (ls: List Text): List Nat :=
  List.foldRight (row below => splitRow 1 row below) (List.replicate w 1) (List.map (splitterRow w) ls)

theorem countsLength (w: Nat): (ls: List Text) -> Fits w ls -> List.length (countsBelow w ls) = w
  | Nil,         fits          => List.lengthReplicate 1 w
  | Cons l rest, Both fit fits =>
    rewrite splitRowLength 1 (splitterRow w l) (countsBelow w rest)
              (rewrite flagsLength w l fit, countsLength w rest fits) in
      countsLength w rest fits

-- One row up: a column's count from the counts below, against the
-- timelines from that column.
theorem countStep (l: Text) (rest: List Text) (r: Nat) (c: Nat) (below: List Nat)
    (ih: (c: Nat) -> List.getOr 1 c below = List.length (timelinesFrom (r + 1) c rest)):
    (if charAt l c == '^' then List.getOr 1 c (Cons 1 below) + List.getOr 1 (Succ c) below else List.getOr 1 c below)
      = List.length (timelinesFrom r c (Cons l rest)) :=
  match e: charAt l c == '^' with
    | True  =>
      match c with
        | Zero   => rewrite List.lengthMap _ _ in Eq.cong Succ (ih 1)
        | Succ b => rewrite List.lengthAppend _ _, List.lengthMap _ _, List.lengthMap _ _, Nat.addOne b, ih b, ih (Succ (Succ b))
    | False => ih c

-- Every column's count is the number of timelines from it.
theorem countsAre (w: Nat): (ls: List Text) -> Fits w ls -> (r: Nat) -> (c: Nat) ->
    List.getOr 1 c (countsBelow w ls) = List.length (timelinesFrom r c ls)
  | Nil,         fits,          r, c => List.getOrReplicate 1 c w
  | Cons l rest, Both fit fits, r, c =>
    calc List.getOr 1 c (countsBelow w (Cons l rest))
      _ = (if List.getOr False c (splitterRow w l) then List.getOr 1 c (Cons 1 (countsBelow w rest)) + List.getOr 1 (Succ c) (countsBelow w rest)
           else List.getOr 1 c (countsBelow w rest))
          := splitRowAt 1 (splitterRow w l) (countsBelow w rest) (rewrite flagsLength w l fit, countsLength w rest fits) c
      _ = (if charAt l c == '^' then List.getOr 1 c (Cons 1 (countsBelow w rest)) + List.getOr 1 (Succ c) (countsBelow w rest)
           else List.getOr 1 c (countsBelow w rest))
          := rewrite flagAt w l c
      _ = List.length (timelinesFrom r c (Cons l rest))
          := countStep l rest r c (countsBelow w rest) (c => countsAre w rest fits (r + 1) c)

-- Part 2 is right: for every input, the printed answer is the number of
-- timelines of the particle from S.
theorem part2Correct (lines: List Text): Maybe.map solvePart2 (parseManifold lines) = part2Spec lines :=
  match e: findStart lines with
    | Nothing           => rfl
    | Just (MkPair r c) => Eq.cong Just (countsAre (gridWidth lines) (List.drop (r + 1) lines) (belowFits lines r) (r + 1) c)
