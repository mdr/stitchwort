-- Rows as vectors: shifting a whole row one place, and a function of each
-- element and its two neighbours (a stencil), for grid puzzles whose rows
-- are `Vec a width`. The fill or pad value stands for a neighbour past either
-- end, so no index is ever out of range. The lemmas give `getOr` of each, the
-- form a proof about one column rewrites with. A file of its own, so that
-- programs using only `Vec.sw` don't check these.

-- Every element one place right, towards the end: element i moves to i + 1,
-- the last one drops off, and `fill` comes in at the front.
-- `[1, 2, 3].shiftRight 0` is `[0, 1, 2]`.
def Vec.shiftRight (fill: a): Vec a n -> Vec a n
  | VNil => VNil
  | VCons x xs => VCons fill (Vec.shiftRight x xs)

-- Every element one place left, towards the front: element i + 1 moves to i,
-- the first one drops off, and `fill` comes in at the end.
-- `[1, 2, 3].shiftLeft 0` is `[2, 3, 0]`.
def Vec.shiftLeft (fill: a): Vec a n -> Vec a n
  | VNil => VNil
  | VCons x xs => VCons (Vec.headOr fill xs) (Vec.shiftLeft fill xs)

-- `f left x right` for every element x and its neighbours, with `pad` for a
-- neighbour past either end: `[1, 2, 3].around 0 (l x r => l + x + r)` is
-- `[3, 6, 5]`. It is `zipWith3 f (v.shiftRight pad) v (v.shiftLeft pad)`
-- (`Vec.aroundShifts`), in one pass.
def Vec.around (pad: a) (f: a -> a -> a -> b) (v: Vec a n): Vec b n := Vec.aroundFrom pad f pad v

-- `around`, with `left` as the first element's left neighbour.
def Vec.aroundFrom (pad: a) (f: a -> a -> a -> b) (left: a): Vec a n -> Vec b n
  | VNil => VNil
  | VCons x rest => VCons (f left x (Vec.headOr pad rest)) (Vec.aroundFrom pad f x rest)

-- Lemmas. Index i of a shifted or `around` row, as `getOr` of the row
-- itself. The left neighbour is written `List.getOr pad i (Cons pad row)`:
-- at `Succ c` it computes to `getOr pad c row`, and at 0 to `pad`.

-- Index i after `shiftRight` is index i of the row with `fill` in front.
theorem Vec.getOrShiftRight (d: a) (fill: a): (v: Vec a n) -> (i: Nat) -> i < n ->
    List.getOr d i (Vec.toList (Vec.shiftRight fill v)) = List.getOr d i (Cons fill (Vec.toList v))
  | VNil, i, h => Void.exfalso (Bool.falseNotTrue h)
  | VCons x xs, Zero, h => rfl
  | VCons x xs, Succ i, h => Vec.getOrShiftRight d x xs i h

-- Index i after `shiftLeft` is index i + 1 before, at every index when the
-- default is the fill.
theorem Vec.getOrShiftLeft (fill: a): (v: Vec a n) -> (i: Nat) ->
    List.getOr fill i (Vec.toList (Vec.shiftLeft fill v)) = List.getOr fill (Succ i) (Vec.toList v)
  | VNil, i => rfl
  | VCons x xs, Zero => Vec.headOrToList fill xs
  | VCons x xs, Succ i => Vec.getOrShiftLeft fill xs i

-- The same with any default, inside the row.
theorem Vec.getOrShiftLeftLt (d: a) (fill: a): (v: Vec a n) -> (i: Nat) -> i < n ->
    List.getOr d i (Vec.toList (Vec.shiftLeft fill v)) = List.getOr fill (Succ i) (Vec.toList v)
  | VNil, i, h => Void.exfalso (Bool.falseNotTrue h)
  | VCons x xs, Zero, h => Vec.headOrToList fill xs
  | VCons x xs, Succ i, h => Vec.getOrShiftLeftLt d fill xs i h

theorem Vec.aroundFromShifts (pad: a) (f: a -> a -> a -> b): (left: a) -> (v: Vec a n) ->
    Vec.aroundFrom pad f left v = Vec.zipWith3 f (Vec.shiftRight left v) v (Vec.shiftLeft pad v)
  | left, VNil => rfl
  | left, VCons x rest => Eq.cong (VCons (f left x (Vec.headOr pad rest))) (Vec.aroundFromShifts pad f x rest)

-- `around` is the two shifts zipped with the row.
theorem Vec.aroundShifts (pad: a) (f: a -> a -> a -> b) (v: Vec a n):
    Vec.around pad f v = Vec.zipWith3 f (Vec.shiftRight pad v) v (Vec.shiftLeft pad v) :=
  Vec.aroundFromShifts pad f pad v

theorem Vec.getOrAroundFrom (d: b) (pad: a) (f: a -> a -> a -> b): (left: a) -> (v: Vec a n) -> (i: Nat) -> i < n ->
    List.getOr d i (Vec.toList (Vec.aroundFrom pad f left v))
      = f (List.getOr pad i (Cons left (Vec.toList v))) (List.getOr pad i (Vec.toList v)) (List.getOr pad (Succ i) (Vec.toList v))
  | left, VNil, i, h => Void.exfalso (Bool.falseNotTrue h)
  | left, VCons x rest, Zero, h => Eq.cong (f left x) (Vec.headOrToList pad rest)
  | left, VCons x rest, Succ i, h => Vec.getOrAroundFrom d pad f x rest i h

-- Index i of `around` is `f` of indices i - 1, i and i + 1 of the row, with
-- `pad` past either end.
theorem Vec.getOrAround (d: b) (pad: a) (f: a -> a -> a -> b) (v: Vec a n) (i: Nat) (h: i < n):
    List.getOr d i (Vec.toList (Vec.around pad f v))
      = f (List.getOr pad i (Cons pad (Vec.toList v))) (List.getOr pad i (Vec.toList v)) (List.getOr pad (Succ i) (Vec.toList v)) :=
  Vec.getOrAroundFrom d pad f pad v i h

def Vec.gridExample: Vec Nat 4 := VCons 1 (VCons 2 (VCons 3 (VCons 4 VNil)))

theorem Vec.shiftRightExample: Vec.toList (Vec.shiftRight 0 Vec.gridExample) = [0, 1, 2, 3] := rfl

theorem Vec.shiftLeftExample: Vec.toList (Vec.shiftLeft 0 Vec.gridExample) = [2, 3, 4, 0] := rfl

theorem Vec.aroundExample: Vec.toList (Vec.around 0 (l x r => l + x + r) Vec.gridExample) = [3, 6, 9, 7] := rfl

test "shiftRight" := Vec.toList (Vec.gridExample.shiftRight 9) == [9, 1, 2, 3]
test "shiftLeft" := Vec.toList (Vec.gridExample.shiftLeft 9) == [2, 3, 4, 9]
test "shifts of one" := Vec.toList (Vec.shiftRight 0 (VCons 5 VNil)) == [0] && Vec.toList (Vec.shiftLeft 0 (VCons 5 VNil)) == [0]
test "shifts of none" := Vec.toList (Vec.shiftRight 0 (VNil: Vec Nat 0)) == [] && Vec.toList (Vec.shiftLeft 0 (VNil: Vec Nat 0)) == []
test "around" := Vec.toList (Vec.gridExample.around 0 (l x r => l * 100 + x * 10 + r)) == [12, 123, 234, 340]
test "around of one" := Vec.toList (Vec.around 7 (l x r => (l, x, r)) (VCons 5 VNil)) == [(7, 5, 7)]
test "around is the shifts" :=
  Vec.toList (Vec.gridExample.around 0 (l x r => l + x + r))
    == Vec.toList (Vec.zipWith3 (l x r => l + x + r) (Vec.gridExample.shiftRight 0) Vec.gridExample (Vec.gridExample.shiftLeft 0))
