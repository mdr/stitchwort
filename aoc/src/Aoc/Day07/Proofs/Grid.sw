-- What both parts' proofs share: every line fits in `gridWidth`, so the
-- program's padded rows of flags lose no splitter, and a flag is the
-- character's (`flagAt`); where S is (`startBounds`).

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

theorem fitsDrop (w: Nat): (n: Nat) -> (lines: List Text) -> Fits w lines -> Fits w (List.drop n lines)
  | Zero,   lines,       fits          => fits
  | Succ n, Nil,         fits          => Trivial
  | Succ n, Cons l rest, Both fit fits => fitsDrop w n rest fits

-- The rows below row r, each fitting in the grid's width.
theorem belowFits (lines: List Text) (r: Nat): Fits (gridWidth lines) (List.drop (r + 1) lines) :=
  fitsDrop (gridWidth lines) (r + 1) lines (foldWidenFits 0 lines)

-- A line's splitter flag in column c says whether the character there is ^.
theorem flagAt (w: Nat) (line: Text) (c: Nat): List.getOr False c (splitterRow w line) = (charAt line c == '^') :=
  rewrite List.getOrPadRight False w c (List.map isSplitter (Text.toList line)) in
    List.getOrMap isSplitter '.' c (Text.toList line)

theorem flagsLength (w: Nat) (line: Text) (fit: line.length <= w): List.length (splitterRow w line) = w :=
  List.padRightLength w False (List.map isSplitter (Text.toList line)) (rewrite List.lengthMap isSplitter (Text.toList line) in fit)

-- Past the end of a line there is empty space.
theorem charAtPast (line: Text) (c: Nat) (h: line.length <= c): charAt line c = '.' :=
  List.getOrPast '.' c (Text.toList line) h

-- Where S is: a row of the diagram, and a column inside the grid.
def StartIn (height: Nat) (width: Nat): Maybe (Nat, Nat) -> Prop
  | Nothing           => Unit
  | Just (MkPair r c) => And (r < height) (c < width)

def ColumnIn (width: Nat): Maybe Nat -> Prop
  | Nothing => Unit
  | Just c  => c < width

theorem columnSucc (n: Nat): (m: Maybe Nat) -> ColumnIn n m -> ColumnIn (Succ n) (Maybe.map Succ m)
  | Nothing, h => Trivial
  | Just c,  h => h

theorem columnOfIn (ch: Char): (xs: List Char) -> ColumnIn (List.length xs) (columnOf ch xs)
  | Nil       => Trivial
  | Cons x xs =>
    match e: x == ch with
      | True  => rfl
      | False => columnSucc (List.length xs) (columnOf ch xs) (columnOfIn ch xs)

theorem firstFoundIn (height: Nat) (w: Nat) (r: Nat) (hr: r < height) (n: Nat) (hn: n <= w):
    (m: Maybe Nat) -> ColumnIn n m -> (below: Maybe (Nat, Nat)) -> StartIn height w below ->
    StartIn height w (firstFound (Maybe.map (c => (r, c)) m) below)
  | Nothing, hm, below, hb => hb
  | Just c,  hm, below, hb => Both hr (Nat.leTrans (Succ c) n w hm hn)

theorem addOneLeft (r: Nat) (n: Nat): (r + 1) + n = Succ (r + n) := rewrite Nat.addOne r

theorem startFromIn (w: Nat): (r: Nat) -> (lines: List Text) -> Fits w lines -> StartIn (r + List.length lines) w (startFrom r lines)
  | r, Nil,         fits          => Trivial
  | r, Cons l rest, Both fit fits =>
    firstFoundIn (r + Succ (List.length rest)) w r (Nat.ltAddSuccSelf r (List.length rest)) (List.length (Text.toList l)) fit
      (columnOf 'S' (Text.toList l)) (columnOfIn 'S' (Text.toList l)) (startFrom (r + 1) rest)
      (rewrite Nat.addSucc r (List.length rest), <- addOneLeft r (List.length rest) in startFromIn w (r + 1) rest fits)

-- S is on a line, inside the grid.
theorem startBounds (lines: List Text): StartIn (List.length lines) (gridWidth lines) (findStart lines) :=
  startFromIn (gridWidth lines) 0 lines (foldWidenFits 0 lines)
