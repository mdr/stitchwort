-- Day 7, proved end to end.

namespace Aoc.Day07.Proofs
import Aoc.Day07 (..)
import Std (Eq)

-- Every line is at most this wide.
def Fits (width: Nat): List Text -> Prop
  | Nil         => Unit
  | Cons l rest => And (l.length <= width) (Fits width rest)

theorem foldWidenGrows (start: Nat): (lines: List Text) -> start <= lines.foldLeft widen start
  | Nil         => Nat.leRefl start
  | Cons l rest =>
    calc start
      _ <= widen start l                         := Nat.leMaxLeft start l.length
      _ <= rest.foldLeft widen (widen start l)   := foldWidenGrows (widen start l) rest

theorem foldWidenFits (start: Nat): (lines: List Text) -> Fits (lines.foldLeft widen start) lines
  | Nil         => Trivial
  | Cons l rest =>
    Both (calc l.length
            _ <= widen start l                       := Nat.leMaxRight start l.length
            _ <= rest.foldLeft widen (widen start l) := foldWidenGrows (widen start l) rest)
         (foldWidenFits (widen start l) rest)

-- A line's splitter flag in column c says whether the character there is ^.
theorem flagAt (w: Nat) (line: Text) (c: Nat): List.getOr False c (splitterRow w line) = (charAt line c == '^') :=
  rewrite List.getOrPadRight False w c (List.map isSplitter (Text.toList line)) in
    List.getOrMap isSplitter '.' c (Text.toList line)

theorem flagsLength (w: Nat) (line: Text) (fit: line.length <= w): List.length (splitterRow w line) = w :=
  List.padRightLength w False (List.map isSplitter (Text.toList line)) (rewrite List.lengthMap isSplitter (Text.toList line) in fit)

-- Part 2 ------------------------------------------------------------------

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

theorem fitsDrop (w: Nat): (n: Nat) -> (lines: List Text) -> Fits w lines -> Fits w (List.drop n lines)
  | Zero,   lines,       fits          => fits
  | Succ n, Nil,         fits          => Trivial
  | Succ n, Cons l rest, Both fit fits => fitsDrop w n rest fits

-- Part 2 is right: for every input, the printed answer is the number of
-- timelines of the particle from S.
theorem part2Correct (lines: List Text): Maybe.map solvePart2 (parseManifold lines) = part2Spec lines :=
  match e: findStart lines with
    | Nothing           => rfl
    | Just (MkPair r c) =>
      Eq.cong Just (countsAre (gridWidth lines) (List.drop (r + 1) lines) (fitsDrop (gridWidth lines) (r + 1) lines (foldWidenFits 0 lines)) (r + 1) c)
