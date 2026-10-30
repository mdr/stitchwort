-- Counting a region's corners counts its sides: the region as a grid of
-- booleans `inside row column`, finite (nothing at row or column `size` or
-- beyond), has as many corners as sides (`cornersEqualSides`).
--
-- A side is a run of fence along a row or a column, so it has a first and a
-- last section, and as many runs start as end along any line
-- (`startsEqualEnds`). Each corner is the end of exactly one run along a
-- row, the one on its vertical side: an outside corner of the plot's own
-- fence, an inside corner of its neighbour's (`rowEndsSplit`). So the
-- corners are the starts and ends of the runs along rows, twice the runs
-- along rows; likewise twice the runs along columns; so their number is the
-- runs along rows plus those along columns.

namespace Aoc.Year2024.Day12.Proofs
import Std (Bool, Eq, Nat)

-- `f 0 + f 1 + … + f (n - 1)`.
def total: (n: Nat) → (f: Nat → Nat) → Nat
  | Zero, f => 0
  | Succ n, f => f 0 + total n (i => f (Succ i))

theorem totalCong: (n: Nat) → (f: Nat → Nat) → (g: Nat → Nat) → ((i: Nat) → f i = g i) → total n f = total n g
  | Zero, f, g, agree => rfl
  | Succ n, f, g, agree => rewrite agree 0, totalCong n (i => f (Succ i)) (i => g (Succ i)) (i => agree (Succ i)) in rfl

theorem totalAdd: (n: Nat) → (f: Nat → Nat) → (g: Nat → Nat) → total n (i => f i + g i) = total n f + total n g
  | Zero, f, g => rfl
  | Succ n, f, g => omega [totalAdd n (i => f (Succ i)) (i => g (Succ i))]

theorem totalZero: (n: Nat) → (f: Nat → Nat) → ((i: Nat) → f i = 0) → total n f = 0
  | Zero, f, zero => rfl
  | Succ n, f, zero => omega [zero 0, totalZero n (i => f (Succ i)) (i => zero (Succ i))]

theorem totalSnoc: (n: Nat) → (f: Nat → Nat) → total (Succ n) f = total n f + f n
  | Zero, f => omega
  | Succ n, f => omega [totalSnoc n (i => f (Succ i))]

-- `g` one place later: `0, g 0, g 1, …`.
def later (g: Nat → Nat): Nat → Nat
  | Zero => 0
  | Succ i => g i

-- Shifting a sum one place either way changes it only at the ends.
theorem totalLater (n: Nat) (g: Nat → Nat): total (Succ n) (later g) + g n = total (Succ n) g :=
  omega [totalSnoc n g, totalCong n (i => later g (Succ i)) g (i => rfl)]

theorem totalEarlier (n: Nat) (g: Nat → Nat): total n (i => g (Succ i)) + g 0 = total n g + g n := omega [totalSnoc n g]

theorem totalSwap: (n: Nat) → (k: Nat) → (f: Nat → Nat → Nat) → total n (r => total k (c => f r c)) = total k (c => total n (r => f r c))
  | Zero, k, f => Eq.sym (totalZero k (c => 0) (c => rfl))
  | Succ n, k, f =>
    rewrite totalSwap n k (r => f (Succ r)) in Eq.sym (totalAdd k (c => f 0 c) (c => total n (r => f (Succ r) c)))

-- `b` one place later, with `first` before it.
def previous (first: Bool) (b: Nat → Bool): Nat → Bool
  | Zero => first
  | Succ i => b i

theorem previousShift (b: Nat → Bool) (first: Bool): (n: Nat) → previous (b 0) (i => b (Succ i)) n = previous first b (Succ n)
  | Zero => rfl
  | Succ n => rfl

-- Along a line, runs of `b` start where the one before isn't in `b`, and
-- end where the one after isn't; the count differs only at the ends.
theorem telescope: (n: Nat) → (b: Nat → Bool) → (first: Bool) →
    total n (i => Bool.toNat (b i ∧ ¬(previous first b i))) + Bool.toNat (first ∧ b 0)
      = total n (i => Bool.toNat (b i ∧ ¬(b (Succ i)))) + Bool.toNat (previous first b n ∧ b n)
  | Zero, b, first => rfl
  | Succ n, b, first =>
    let rest := telescope n (i => b (Succ i)) (b 0)
    let shifted :=
      totalCong n (i => Bool.toNat (b (Succ i) ∧ ¬(previous first b (Succ i)))) (i => Bool.toNat (b (Succ i) ∧ ¬(previous (b 0) (i => b (Succ i)) i)))
        (i => rewrite previousShift b first i in rfl)
    rewrite <- shifted, previousShift b first n at rest in
      match atZero: b 0, atOne: b 1, before: first with
        | True, True, True => omega [rest]
        | True, True, False => omega [rest]
        | True, False, True => omega [rest]
        | True, False, False => omega [rest]
        | False, True, True => omega [rest]
        | False, True, False => omega [rest]
        | False, False, True => omega [rest]
        | False, False, False => omega [rest]

-- As many runs start as end, on a line with nothing at `n`.
theorem startsEqualEnds (n: Nat) (b: Nat → Bool) (stop: b n = False):
    total n (i => Bool.toNat (b i ∧ ¬(previous False b i))) = total n (i => Bool.toNat (b i ∧ ¬(b (Succ i)))) :=
  let both := telescope n b False
  rewrite stop, Bool.andFalse (previous False b n) at both in omega [both]

-- The grid around a plot.
def above (inside: Nat → Nat → Bool) (row: Nat) (column: Nat): Bool :=
  match row with
    | Zero => False
    | Succ up => inside up column

def below (inside: Nat → Nat → Bool) (row: Nat) (column: Nat): Bool := inside (Succ row) column

def leftOf (inside: Nat → Nat → Bool) (row: Nat) (column: Nat): Bool :=
  match column with
    | Zero => False
    | Succ before => inside row before

def rightOf (inside: Nat → Nat → Bool) (row: Nat) (column: Nat): Bool := inside row (Succ column)

-- Fence on each side of a plot: the plot is in, its neighbour isn't.
def fenceUp (inside: Nat → Nat → Bool) (row: Nat) (column: Nat): Bool := inside row column ∧ ¬(above inside row column)
def fenceDown (inside: Nat → Nat → Bool) (row: Nat) (column: Nat): Bool := inside row column ∧ ¬(below inside row column)
def fenceLeft (inside: Nat → Nat → Bool) (row: Nat) (column: Nat): Bool := inside row column ∧ ¬(leftOf inside row column)
def fenceRight (inside: Nat → Nat → Bool) (row: Nat) (column: Nat): Bool := inside row column ∧ ¬(rightOf inside row column)

-- The first section of a side: fence with no fence on the same side before
-- it, left of it for a side above or below, above it for one on the left
-- or right.
def startUp (inside: Nat → Nat → Bool) (row: Nat) (column: Nat): Bool := fenceUp inside row column ∧ ¬(leftOf (fenceUp inside) row column)
def startDown (inside: Nat → Nat → Bool) (row: Nat) (column: Nat): Bool := fenceDown inside row column ∧ ¬(leftOf (fenceDown inside) row column)
def startLeft (inside: Nat → Nat → Bool) (row: Nat) (column: Nat): Bool := fenceLeft inside row column ∧ ¬(above (fenceLeft inside) row column)
def startRight (inside: Nat → Nat → Bool) (row: Nat) (column: Nat): Bool := fenceRight inside row column ∧ ¬(above (fenceRight inside) row column)

-- The last section of a side.
def endUp (inside: Nat → Nat → Bool) (row: Nat) (column: Nat): Bool := fenceUp inside row column ∧ ¬(rightOf (fenceUp inside) row column)
def endDown (inside: Nat → Nat → Bool) (row: Nat) (column: Nat): Bool := fenceDown inside row column ∧ ¬(rightOf (fenceDown inside) row column)
def endLeft (inside: Nat → Nat → Bool) (row: Nat) (column: Nat): Bool := fenceLeft inside row column ∧ ¬(below (fenceLeft inside) row column)
def endRight (inside: Nat → Nat → Bool) (row: Nat) (column: Nat): Bool := fenceRight inside row column ∧ ¬(below (fenceRight inside) row column)

-- The sides starting at a plot.
def starts (inside: Nat → Nat → Bool) (row: Nat) (column: Nat): Nat :=
  Bool.toNat (startUp inside row column) + Bool.toNat (startDown inside row column) + Bool.toNat (startLeft inside row column)
    + Bool.toNat (startRight inside row column)

-- A corner of a plot, between its `vertical` and `horizontal` neighbours:
-- outside, with neither in, or inside, with both in but not the plot
-- `diagonal`ly across.
def convex (plot: Bool) (vertical: Bool) (horizontal: Bool): Bool := plot ∧ ¬vertical ∧ ¬horizontal
def concave (plot: Bool) (vertical: Bool) (horizontal: Bool) (diagonal: Bool): Bool := plot ∧ vertical ∧ horizontal ∧ ¬diagonal

-- The corners of a plot, up and left of it and so on, outside and inside.
def convexUpLeft (inside: Nat → Nat → Bool) (row: Nat) (column: Nat): Nat :=
  Bool.toNat (convex (inside row column) (above inside row column) (leftOf inside row column))

def concaveUpLeft (inside: Nat → Nat → Bool) (row: Nat) (column: Nat): Nat :=
  Bool.toNat (concave (inside row column) (above inside row column) (leftOf inside row column) (above (leftOf inside) row column))

def convexUpRight (inside: Nat → Nat → Bool) (row: Nat) (column: Nat): Nat :=
  Bool.toNat (convex (inside row column) (above inside row column) (rightOf inside row column))

def concaveUpRight (inside: Nat → Nat → Bool) (row: Nat) (column: Nat): Nat :=
  Bool.toNat (concave (inside row column) (above inside row column) (rightOf inside row column) (above (rightOf inside) row column))

def convexDownLeft (inside: Nat → Nat → Bool) (row: Nat) (column: Nat): Nat :=
  Bool.toNat (convex (inside row column) (below inside row column) (leftOf inside row column))

def concaveDownLeft (inside: Nat → Nat → Bool) (row: Nat) (column: Nat): Nat :=
  Bool.toNat (concave (inside row column) (below inside row column) (leftOf inside row column) (below (leftOf inside) row column))

def convexDownRight (inside: Nat → Nat → Bool) (row: Nat) (column: Nat): Nat :=
  Bool.toNat (convex (inside row column) (below inside row column) (rightOf inside row column))

def concaveDownRight (inside: Nat → Nat → Bool) (row: Nat) (column: Nat): Nat :=
  Bool.toNat (concave (inside row column) (below inside row column) (rightOf inside row column) (below (rightOf inside) row column))

def cornerUpLeft (inside: Nat → Nat → Bool) (row: Nat) (column: Nat): Nat := convexUpLeft inside row column + concaveUpLeft inside row column
def cornerUpRight (inside: Nat → Nat → Bool) (row: Nat) (column: Nat): Nat := convexUpRight inside row column + concaveUpRight inside row column
def cornerDownLeft (inside: Nat → Nat → Bool) (row: Nat) (column: Nat): Nat := convexDownLeft inside row column + concaveDownLeft inside row column
def cornerDownRight (inside: Nat → Nat → Bool) (row: Nat) (column: Nat): Nat := convexDownRight inside row column + concaveDownRight inside row column

def corners (inside: Nat → Nat → Bool) (row: Nat) (column: Nat): Nat :=
  cornerUpLeft inside row column + cornerUpRight inside row column + cornerDownLeft inside row column + cornerDownRight inside row column

-- One end of a run along a row: an outside corner of the plot, or an
-- inside corner of the plot next to it along the row.
theorem rowEndsSplit: (plot: Bool) → (out: Bool) → (side: Bool) → (sideOut: Bool) →
    Bool.toNat ((plot ∧ ¬out) ∧ ¬(side ∧ ¬sideOut)) = Bool.toNat (convex plot out side) + Bool.toNat (concave side sideOut plot out) :=
  cases

-- One end of a run along a column, likewise.
theorem columnEndsSplit: (plot: Bool) → (out: Bool) → (side: Bool) → (sideOut: Bool) →
    Bool.toNat ((plot ∧ ¬out) ∧ ¬(side ∧ ¬sideOut)) = Bool.toNat (convex plot side out) + Bool.toNat (concave side plot sideOut out) :=
  cases

-- No inside corner without the horizontal neighbour, or the plot itself.
theorem concaveNoHorizontal: (plot: Bool) → (vertical: Bool) → (diagonal: Bool) → concave plot vertical False diagonal = False
  | True, True, diagonal => rfl
  | True, False, diagonal => rfl
  | False, vertical, diagonal => rfl

theorem concaveNoVertical: (plot: Bool) → (horizontal: Bool) → (diagonal: Bool) → concave plot False horizontal diagonal = False
  | True, horizontal, diagonal => rfl
  | False, horizontal, diagonal => rfl

-- A plot's sections of fence above it that start or end a side are the
-- corners on that side: outside corners of the plot, or inside corners of
-- the plots either side of it.
theorem cellUp (inside: Nat → Nat → Bool): (row: Nat) → (column: Nat) →
    Bool.toNat (startUp inside row column) + Bool.toNat (endUp inside row column)
      = convexUpLeft inside row column + convexUpRight inside row column + later (concaveUpRight inside row) column
        + concaveUpLeft inside row (Succ column)
  | Zero, Zero =>
    omega [rowEndsSplit (inside 0 0) False False False, rowEndsSplit (inside 0 0) False (inside 0 1) False]
  | Zero, Succ before =>
    omega [
      rowEndsSplit (inside 0 (Succ before)) False (inside 0 before) False,
      rowEndsSplit (inside 0 (Succ before)) False (inside 0 (Succ (Succ before))) False
    ]
  | Succ up, Zero =>
    omega [
      rowEndsSplit (inside (Succ up) 0) (inside up 0) False False,
      rowEndsSplit (inside (Succ up) 0) (inside up 0) (inside (Succ up) 1) (inside up 1)
    ]
  | Succ up, Succ before =>
    omega [
      rowEndsSplit (inside (Succ up) (Succ before)) (inside up (Succ before)) (inside (Succ up) before) (inside up before),
      rowEndsSplit (inside (Succ up) (Succ before)) (inside up (Succ before)) (inside (Succ up) (Succ (Succ before))) (inside up (Succ (Succ before)))
    ]

theorem cellDown (inside: Nat → Nat → Bool) (row: Nat): (column: Nat) →
    Bool.toNat (startDown inside row column) + Bool.toNat (endDown inside row column)
      = convexDownLeft inside row column + convexDownRight inside row column + later (concaveDownRight inside row) column
        + concaveDownLeft inside row (Succ column)
  | Zero =>
    omega [
      rowEndsSplit (inside row 0) (inside (Succ row) 0) False False,
      rowEndsSplit (inside row 0) (inside (Succ row) 0) (inside row 1) (inside (Succ row) 1)
    ]
  | Succ before =>
    omega [
      rowEndsSplit (inside row (Succ before)) (inside (Succ row) (Succ before)) (inside row before) (inside (Succ row) before),
      rowEndsSplit (inside row (Succ before)) (inside (Succ row) (Succ before)) (inside row (Succ (Succ before))) (inside (Succ row) (Succ (Succ before)))
    ]

-- Likewise down a column, for fence left and right of a plot.
theorem cellLeft (inside: Nat → Nat → Bool) (column: Nat): (row: Nat) →
    Bool.toNat (startLeft inside row column) + Bool.toNat (endLeft inside row column)
      = convexUpLeft inside row column + convexDownLeft inside row column + later (r => concaveDownLeft inside r column) row
        + concaveUpLeft inside (Succ row) column
  | Zero =>
    omega [
      columnEndsSplit (inside 0 column) (leftOf inside 0 column) False False,
      columnEndsSplit (inside 0 column) (leftOf inside 0 column) (inside 1 column) (leftOf inside 1 column)
    ]
  | Succ up =>
    omega [
      columnEndsSplit (inside (Succ up) column) (leftOf inside (Succ up) column) (inside up column) (leftOf inside up column),
      columnEndsSplit (inside (Succ up) column) (leftOf inside (Succ up) column) (inside (Succ (Succ up)) column) (leftOf inside (Succ (Succ up)) column)
    ]

theorem cellRight (inside: Nat → Nat → Bool) (column: Nat): (row: Nat) →
    Bool.toNat (startRight inside row column) + Bool.toNat (endRight inside row column)
      = convexUpRight inside row column + convexDownRight inside row column + later (r => concaveDownRight inside r column) row
        + concaveUpRight inside (Succ row) column
  | Zero =>
    omega [
      columnEndsSplit (inside 0 column) (inside 0 (Succ column)) False False,
      columnEndsSplit (inside 0 column) (inside 0 (Succ column)) (inside 1 column) (inside 1 (Succ column))
    ]
  | Succ up =>
    omega [
      columnEndsSplit (inside (Succ up) column) (inside (Succ up) (Succ column)) (inside up column) (inside up (Succ column)),
      columnEndsSplit (inside (Succ up) column) (inside (Succ up) (Succ column)) (inside (Succ (Succ up)) column) (inside (Succ (Succ up)) (Succ column))
    ]

theorem totalDouble: (n: Nat) → (f: Nat → Nat) → total n (i => 2 * f i) = 2 * total n f
  | Zero, f => rfl
  | Succ n, f => omega [totalDouble n (i => f (Succ i))]

theorem totalAdd4 (n: Nat) (f: Nat → Nat) (g: Nat → Nat) (h: Nat → Nat) (k: Nat → Nat):
    total n (i => f i + g i + h i + k i) = total n f + total n g + total n h + total n k :=
  omega [
    totalAdd n (i => f i + g i + h i) k,
    totalAdd n (i => f i + g i) h,
    totalAdd n f g
  ]

-- Along a row with nothing at `Succ last`, the corners above and below the
-- plots are twice the sides above and below them.
theorem rowCorners (inside: Nat → Nat → Bool) (last: Nat) (row: Nat) (edge: inside row (Succ last) = False):
    total (Succ last) (column => corners inside row column)
      = 2 * total (Succ last) (column => Bool.toNat (startUp inside row column))
        + 2 * total (Succ last) (column => Bool.toNat (startDown inside row column)) :=
  let size := Succ last
  let upCells :=
    Eq.trans
      (totalCong size (column => Bool.toNat (startUp inside row column) + Bool.toNat (endUp inside row column))
        (column =>
          convexUpLeft inside row column + convexUpRight inside row column + later (concaveUpRight inside row) column
            + concaveUpLeft inside row (Succ column)) (column => cellUp inside row column))
      (totalAdd4 size (convexUpLeft inside row) (convexUpRight inside row) (later (concaveUpRight inside row)) (column => concaveUpLeft inside row (Succ column)))
  let downCells :=
    Eq.trans
      (totalCong size (column => Bool.toNat (startDown inside row column) + Bool.toNat (endDown inside row column))
        (column =>
          convexDownLeft inside row column + convexDownRight inside row column + later (concaveDownRight inside row) column
            + concaveDownLeft inside row (Succ column)) (column => cellDown inside row column))
      (totalAdd4 size (convexDownLeft inside row) (convexDownRight inside row) (later (concaveDownRight inside row))
        (column => concaveDownLeft inside row (Succ column)))
  let upEnds := startsEqualEnds size (fenceUp inside row) (rewrite edge in rfl)
  let upStarts :=
    totalCong size (column => Bool.toNat (startUp inside row column)) (column => Bool.toNat (fenceUp inside row column ∧ ¬(previous False (fenceUp inside row) column)))
      (column =>
        match column with
          | Zero => rfl
          | Succ before => rfl)
  let downEnds := startsEqualEnds size (fenceDown inside row) (rewrite edge in rfl)
  let downStarts :=
    totalCong size (column => Bool.toNat (startDown inside row column))
      (column => Bool.toNat (fenceDown inside row column ∧ ¬(previous False (fenceDown inside row) column)))
      (column =>
        match column with
          | Zero => rfl
          | Succ before => rfl)
  let upRightLast: concaveUpRight inside row last = 0 :=
    rewrite edge, concaveNoHorizontal (inside row last) (above inside row last) (above (rightOf inside) row last) in rfl
  let upLeftFirst: concaveUpLeft inside row 0 = 0 := rewrite concaveNoHorizontal (inside row 0) (above inside row 0) (above (leftOf inside) row 0) in rfl
  let upLeftLast: concaveUpLeft inside row size = 0 := rewrite edge in rfl
  let downRightLast: concaveDownRight inside row last = 0 :=
    rewrite edge, concaveNoHorizontal (inside row last) (below inside row last) (below (rightOf inside) row last) in rfl
  let downLeftFirst: concaveDownLeft inside row 0 = 0 :=
    rewrite concaveNoHorizontal (inside row 0) (below inside row 0) (below (leftOf inside) row 0) in rfl
  let downLeftLast: concaveDownLeft inside row size = 0 := rewrite edge in rfl
  omega [
    totalAdd4 size (cornerUpLeft inside row) (cornerUpRight inside row) (cornerDownLeft inside row) (cornerDownRight inside row),
    totalAdd size (convexUpLeft inside row) (concaveUpLeft inside row),
    totalAdd size (convexUpRight inside row) (concaveUpRight inside row),
    totalAdd size (convexDownLeft inside row) (concaveDownLeft inside row),
    totalAdd size (convexDownRight inside row) (concaveDownRight inside row),
    upCells,
    downCells,
    upEnds,
    upStarts,
    downEnds,
    downStarts,
    totalLater last (concaveUpRight inside row),
    upRightLast,
    totalEarlier size (concaveUpLeft inside row),
    upLeftFirst,
    upLeftLast,
    totalLater last (concaveDownRight inside row),
    downRightLast,
    totalEarlier size (concaveDownLeft inside row),
    downLeftFirst,
    downLeftLast,
    totalAdd size (column => Bool.toNat (startUp inside row column)) (column => Bool.toNat (endUp inside row column)),
    totalAdd size (column => Bool.toNat (startDown inside row column)) (column => Bool.toNat (endDown inside row column))
  ]

-- Down a column with nothing at `Succ last`, the corners left and right of
-- the plots are twice the sides left and right of them.
theorem columnCorners (inside: Nat → Nat → Bool) (last: Nat) (column: Nat) (edge: inside (Succ last) column = False):
    total (Succ last) (row => corners inside row column)
      = 2 * total (Succ last) (row => Bool.toNat (startLeft inside row column))
        + 2 * total (Succ last) (row => Bool.toNat (startRight inside row column)) :=
  let size := Succ last
  let leftCells :=
    Eq.trans
      (totalCong size (row => Bool.toNat (startLeft inside row column) + Bool.toNat (endLeft inside row column))
        (row =>
          convexUpLeft inside row column + convexDownLeft inside row column + later (r => concaveDownLeft inside r column) row
            + concaveUpLeft inside (Succ row) column) (row => cellLeft inside column row))
      (totalAdd4 size (row => convexUpLeft inside row column) (row => convexDownLeft inside row column) (later (r => concaveDownLeft inside r column))
        (row => concaveUpLeft inside (Succ row) column))
  let rightCells :=
    Eq.trans
      (totalCong size (row => Bool.toNat (startRight inside row column) + Bool.toNat (endRight inside row column))
        (row =>
          convexUpRight inside row column + convexDownRight inside row column + later (r => concaveDownRight inside r column) row
            + concaveUpRight inside (Succ row) column) (row => cellRight inside column row))
      (totalAdd4 size (row => convexUpRight inside row column) (row => convexDownRight inside row column) (later (r => concaveDownRight inside r column))
        (row => concaveUpRight inside (Succ row) column))
  let leftEnds := startsEqualEnds size (row => fenceLeft inside row column) (rewrite edge in rfl)
  let leftStarts :=
    totalCong size (row => Bool.toNat (startLeft inside row column))
      (row => Bool.toNat (fenceLeft inside row column ∧ ¬(previous False (r => fenceLeft inside r column) row)))
      (row =>
        match row with
          | Zero => rfl
          | Succ before => rfl)
  let rightEnds := startsEqualEnds size (row => fenceRight inside row column) (rewrite edge in rfl)
  let rightStarts :=
    totalCong size (row => Bool.toNat (startRight inside row column))
      (row => Bool.toNat (fenceRight inside row column ∧ ¬(previous False (r => fenceRight inside r column) row)))
      (row =>
        match row with
          | Zero => rfl
          | Succ before => rfl)
  let downLeftLast: concaveDownLeft inside last column = 0 :=
    rewrite edge, concaveNoVertical (inside last column) (leftOf inside last column) (below (leftOf inside) last column) in rfl
  let upLeftFirst: concaveUpLeft inside 0 column = 0 := rewrite concaveNoVertical (inside 0 column) (leftOf inside 0 column) (above (leftOf inside) 0 column) in rfl
  let upLeftLast: concaveUpLeft inside size column = 0 := rewrite edge in rfl
  let downRightLast: concaveDownRight inside last column = 0 :=
    rewrite edge, concaveNoVertical (inside last column) (rightOf inside last column) (below (rightOf inside) last column) in rfl
  let upRightFirst: concaveUpRight inside 0 column = 0 :=
    rewrite concaveNoVertical (inside 0 column) (rightOf inside 0 column) (above (rightOf inside) 0 column) in rfl
  let upRightLast: concaveUpRight inside size column = 0 := rewrite edge in rfl
  omega [
    totalAdd4 size (row => cornerUpLeft inside row column) (row => cornerUpRight inside row column) (row => cornerDownLeft inside row column)
      (row => cornerDownRight inside row column),
    totalAdd size (row => convexUpLeft inside row column) (row => concaveUpLeft inside row column),
    totalAdd size (row => convexUpRight inside row column) (row => concaveUpRight inside row column),
    totalAdd size (row => convexDownLeft inside row column) (row => concaveDownLeft inside row column),
    totalAdd size (row => convexDownRight inside row column) (row => concaveDownRight inside row column),
    leftCells,
    rightCells,
    leftEnds,
    leftStarts,
    rightEnds,
    rightStarts,
    totalLater last (row => concaveDownLeft inside row column),
    downLeftLast,
    totalEarlier size (row => concaveUpLeft inside row column),
    upLeftFirst,
    upLeftLast,
    totalLater last (row => concaveDownRight inside row column),
    downRightLast,
    totalEarlier size (row => concaveUpRight inside row column),
    upRightFirst,
    upRightLast,
    totalAdd size (row => Bool.toNat (startLeft inside row column)) (row => Bool.toNat (endLeft inside row column)),
    totalAdd size (row => Bool.toNat (startRight inside row column)) (row => Bool.toNat (endRight inside row column))
  ]

-- A finite region has as many corners as sides: nothing at row or column
-- `Succ last`, so none beyond.
theorem cornersEqualSides (inside: Nat → Nat → Bool) (last: Nat) (right: (row: Nat) → inside row (Succ last) = False)
    (bottom: (column: Nat) → inside (Succ last) column = False):
    total (Succ last) (row => total (Succ last) (column => corners inside row column))
      = total (Succ last) (row => total (Succ last) (column => starts inside row column)) :=
  let size := Succ last
  let rowStarts := (row: Nat) => total size (column => Bool.toNat (startUp inside row column)) + total size (column => Bool.toNat (startDown inside row column))
  let columnStarts := (column: Nat) => total size (row => Bool.toNat (startLeft inside row column)) + total size (row => Bool.toNat (startRight inside row column))
  let byRows :=
    Eq.trans
      (totalCong size (row => total size (column => corners inside row column)) (row => 2 * rowStarts row) (row =>
        omega [rowCorners inside last row (right row)]))
      (totalDouble size rowStarts)
  let byColumns :=
    Eq.trans (totalSwap size size (row column => corners inside row column))
      (Eq.trans
        (totalCong size (column => total size (row => corners inside row column)) (column => 2 * columnStarts column) (column =>
          omega [columnCorners inside last column (bottom column)]))
        (totalDouble size columnStarts))
  let startsSplit :=
    Eq.trans
      (totalCong size (row => total size (column => starts inside row column))
        (row =>
          rowStarts row
            + total size (column => Bool.toNat (startLeft inside row column) + Bool.toNat (startRight inside row column)))
        (row =>
          omega [
            totalAdd4 size (column => Bool.toNat (startUp inside row column)) (column => Bool.toNat (startDown inside row column))
              (column => Bool.toNat (startLeft inside row column)) (column => Bool.toNat (startRight inside row column)),
            totalAdd size (column => Bool.toNat (startLeft inside row column)) (column => Bool.toNat (startRight inside row column))
          ]))
      (totalAdd size rowStarts (row => total size (column => Bool.toNat (startLeft inside row column) + Bool.toNat (startRight inside row column))))
  let sidesSwapped :=
    Eq.trans (totalSwap size size (row column => Bool.toNat (startLeft inside row column) + Bool.toNat (startRight inside row column)))
      (totalCong size (column => total size (row => Bool.toNat (startLeft inside row column) + Bool.toNat (startRight inside row column))) columnStarts
        (column => totalAdd size (row => Bool.toNat (startLeft inside row column)) (row => Bool.toNat (startRight inside row column))))
  omega [byRows, byColumns, startsSplit, sidesSwapped]
