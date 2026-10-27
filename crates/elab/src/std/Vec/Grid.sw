-- Rows as vectors: shifting a whole row one place, and a function of each
-- element and its two neighbours (a stencil), for grid puzzles whose rows
-- are `Vec a width`. The fill or pad value stands for a neighbour past either
-- end, so no index is ever out of range. The lemmas give `getOr` of each, the
-- form a proof about one column rewrites with. A file of its own, so that
-- programs using only `Vec.sw` don't check these.

-- Every element one place right, towards the end: element i moves to i + 1,
-- the last one drops off, and `fill` comes in at the front.
-- `[1, 2, 3].shiftRight 0` is `[0, 1, 2]`.
def Vec.shiftRight: Vec a n → (fill: a) → Vec a n
  | VNil, fill => VNil
  | VCons x xs, fill => VCons fill (Vec.shiftRight xs x)

-- Every element one place left, towards the front: element i + 1 moves to i,
-- the first one drops off, and `fill` comes in at the end.
-- `[1, 2, 3].shiftLeft 0` is `[2, 3, 0]`.
def Vec.shiftLeft: Vec a n → (fill: a) → Vec a n
  | VNil, fill => VNil
  | VCons x xs, fill => VCons (Vec.headOr xs fill) (Vec.shiftLeft xs fill)

-- `f left x right` for every element x and its neighbours, with `pad` for a
-- neighbour past either end: `[1, 2, 3].around 0 (l x r => l + x + r)` is
-- `[3, 6, 5]`. It is `zipWith3 f (v.shiftRight pad) v (v.shiftLeft pad)`
-- (`Vec.aroundShifts`), in one pass.
def Vec.around (v: Vec a n) (pad: a) (f: a → a → a → b): Vec b n := Vec.aroundFrom pad f pad v

-- `around`, with `left` as the first element's left neighbour.
@[noReceiver]
def Vec.aroundFrom (pad: a) (f: a → a → a → b) (left: a): Vec a n → Vec b n
  | VNil => VNil
  | VCons x rest => VCons (f left x (Vec.headOr rest pad)) (Vec.aroundFrom pad f x rest)

-- Lemmas. Index i of a shifted or `around` row, as `getOr` of the row
-- itself. The left neighbour is written `Vec.getOr (VCons pad row) i pad`:
-- at `Succ c` it computes to `Vec.getOr row c pad`, and at 0 to `pad`.

-- Index i after `shiftRight` is index i of the row with `fill` in front.
theorem Vec.getOrShiftRight: (v: Vec a n) → (i: Nat) → (d: a) → (fill: a) → i < n →
    Vec.getOr (Vec.shiftRight v fill) i d = Vec.getOr (VCons fill v) i d
  | VNil, i, d, fill, h => Void.exfalso (Bool.falseNotTrue h)
  | VCons x xs, Zero, d, fill, h => rfl
  | VCons x xs, Succ i, d, fill, h => Vec.getOrShiftRight xs i d x h

-- Index i after `shiftLeft` is index i + 1 before, at every index when the
-- default is the fill.
theorem Vec.getOrShiftLeft: (v: Vec a n) → (fill: a) → (i: Nat) →
    Vec.getOr (Vec.shiftLeft v fill) i fill = Vec.getOr v (Succ i) fill
  | VNil, fill, i => rfl
  | VCons x xs, fill, Zero => Vec.headOrGetOr xs fill
  | VCons x xs, fill, Succ i => Vec.getOrShiftLeft xs fill i

-- The same with any default, inside the row.
theorem Vec.getOrShiftLeftLt: (v: Vec a n) → (i: Nat) → (d: a) → (fill: a) → i < n →
    Vec.getOr (Vec.shiftLeft v fill) i d = Vec.getOr v (Succ i) fill
  | VNil, i, d, fill, h => Void.exfalso (Bool.falseNotTrue h)
  | VCons x xs, Zero, d, fill, h => Vec.headOrGetOr xs fill
  | VCons x xs, Succ i, d, fill, h => Vec.getOrShiftLeftLt xs i d fill h

theorem Vec.aroundFromShifts: (v: Vec a n) → (pad: a) → (left: a) → (f: a → a → a → b) →
    Vec.aroundFrom pad f left v = Vec.zipWith3 (Vec.shiftRight v left) v (Vec.shiftLeft v pad) f
  | VNil, pad, left, f => rfl
  | VCons x rest, pad, left, f => Eq.cong (VCons (f left x (Vec.headOr rest pad))) (Vec.aroundFromShifts rest pad x f)

-- `around` is the two shifts zipped with the row.
theorem Vec.aroundShifts (v: Vec a n) (pad: a) (f: a → a → a → b):
    Vec.around v pad f = Vec.zipWith3 (Vec.shiftRight v pad) v (Vec.shiftLeft v pad) f :=
  Vec.aroundFromShifts v pad pad f

theorem Vec.getOrAroundFrom: (v: Vec a n) → (i: Nat) → (d: b) → (pad: a) → (left: a) → i < n → (f: a → a → a → b) →
    Vec.getOr (Vec.aroundFrom pad f left v) i d = f (Vec.getOr (VCons left v) i pad) (Vec.getOr v i pad) (Vec.getOr v (Succ i) pad)
  | VNil, i, d, pad, left, h, f => Void.exfalso (Bool.falseNotTrue h)
  | VCons x rest, Zero, d, pad, left, h, f => Eq.cong (f left x) (Vec.headOrGetOr rest pad)
  | VCons x rest, Succ i, d, pad, left, h, f => Vec.getOrAroundFrom rest i d pad x h f

-- Index i of `around` is `f` of indices i - 1, i and i + 1 of the row, with
-- `pad` past either end.
theorem Vec.getOrAround (v: Vec a n) (i: Nat) (d: b) (pad: a) (h: i < n) (f: a → a → a → b):
    Vec.getOr (Vec.around v pad f) i d = f (Vec.getOr (VCons pad v) i pad) (Vec.getOr v i pad) (Vec.getOr v (Succ i) pad) :=
  Vec.getOrAroundFrom v i d pad pad h f

def Vec.gridExample: Vec Nat 4 := VCons 1 (VCons 2 (VCons 3 (VCons 4 VNil)))

theorem Vec.shiftRightExample: Vec.toList (Vec.shiftRight Vec.gridExample 0) = [0, 1, 2, 3] := rfl

theorem Vec.shiftLeftExample: Vec.toList (Vec.shiftLeft Vec.gridExample 0) = [2, 3, 4, 0] := rfl

theorem Vec.aroundExample: Vec.toList (Vec.around Vec.gridExample 0 (l x r => l + x + r)) = [3, 6, 9, 7] := rfl

test "shiftRight" := Vec.toList (Vec.gridExample.shiftRight 9) == [9, 1, 2, 3]
test "shiftLeft" := Vec.toList (Vec.gridExample.shiftLeft 9) == [2, 3, 4, 9]
test "shifts of one" := Vec.toList (Vec.shiftRight (VCons 5 VNil) 0) == [0] ∧ Vec.toList (Vec.shiftLeft (VCons 5 VNil) 0) == [0]
test "shifts of none" := Vec.toList (Vec.shiftRight (VNil: Vec Nat 0) 0) == [] ∧ Vec.toList (Vec.shiftLeft (VNil: Vec Nat 0) 0) == []
test "around" := Vec.toList (Vec.gridExample.around 0 (l x r => l * 100 + x * 10 + r)) == [12, 123, 234, 340]
test "around of one" := Vec.toList (Vec.around (VCons 5 VNil) 7 (l x r => (l, x, r))) == [(7, 5, 7)]
test "around is the shifts" :=
  Vec.toList (Vec.gridExample.around 0 (l x r => l + x + r))
    == Vec.toList (Vec.zipWith3 (Vec.gridExample.shiftRight 0) Vec.gridExample (Vec.gridExample.shiftLeft 0) (l x r => l + x + r))
