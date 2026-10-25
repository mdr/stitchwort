-- Numbers at `Int`: literals take their type from what's expected, and
-- arithmetic and comparisons are typed a group at a time
-- (docs/proposals/integers.md, "Literals" and "Numeric expressions").

import Std (List)

-- Literals: `k` is `OfNat k`, `-k` is `NegSucc (k - 1)`, and `-0` is `OfNat 0`.
theorem lit: (5: Int) = OfNat 5 := rfl

theorem negLit: (-5: Int) = NegSucc 4 := rfl

theorem negZero: (-0: Int) = OfNat 0 := rfl

-- Expected types reach literals inside constructors and lists.
theorem inSome: (Some 5: Option Int) = Some (OfNat 5) := rfl

theorem inList: ([1, 2, -3]: List Int) = [OfNat 1, OfNat 2, NegSucc 2] := rfl

theorem inPair: (MkPair 1 (-2): Pair Nat Int) = MkPair 1 (NegSucc 1) := rfl

-- A definition that unfolds to `Int` takes literals too.
def Price: Type := Int

theorem price: (7: Price) = OfNat 7 := rfl

-- The minus sign makes a group `Int`, wherever it is.
theorem minusDecides: 3 - 5 = -2 := rfl

theorem negGroup: -(3 - 5) = 2 := rfl

-- Prefix minus binds tighter than `%`: the dial.
theorem dial: -18 % 100 = 82 := rfl

theorem dialBracketed: -(18 % 100) = -18 := rfl

-- With nothing to say otherwise, a group is `Nat`, as before.
def natDiff: Nat := 3 - 5

theorem natDiffZero: natDiff = 0 := rfl

def intDiff: Int :=
  let n: Int := 3 - 5
  n

theorem intDiffNeg: intDiff = -2 := rfl

def doubled: List Nat := List.map [1, 2] (x => x + 1)

-- A leaf without literals decides, wherever it is in the group.
def addOne (x: Int): Int := x + 1

def oneMinus (x: Int): Int := 1 - x

def timesMinusTwo (x: Int): Int := x * -2

def isZero (x: Int): Bool := 0 == x

def isZeroRight (x: Int): Bool := x == 0

def notZero (x: Int): Prop := 0 ≠ x

def zeroEq (x: Int): Prop := 0 = x

def negative (x: Int): Prop := x < 0

def pick (c: Bool) (i: Int): Int := (if c then 1 else 2) + i

def dialOf (pos: Int): Int := pos % 100

def someFive (m: Option Int): Prop := Some 5 = m

def empty (xs: List Int): Prop := xs = []

-- A `Nat` becomes an `Int` explicitly.
def shifted (n: Nat) (i: Int): Int := n.toInt + i

-- A generic function's literal argument defaults when it's checked, so
-- the `Int` has to come first or be written.
def chooseFirst [a: Type] (x: a) (y: a): a := x

def firstWritten (i: Int): Int := chooseFirst (5: Int) i

def firstAfter (i: Int): Int := chooseFirst i 5

-- Precedence.
def absOfNeg (x: Int): Int := (-x).abs

def negOfAbs (x: Int): Int := -x.abs

test "x + 1" := addOne (-1) == 0
test "1 - x" := oneMinus 3 == -2
test "x * -2" := timesMinusTwo 3 == -6
test "0 == x" := isZero 0
test "x == 0" := if isZeroRight 1 then False else True
test "if leaf" := pick True (-1) == 0
test "pos % 100" := dialOf (-18) == 82
test "n.toInt + i" := shifted 2 (-5) == -3
test "chooseFirst i 5" := firstAfter (-1) == -1
test "(-x).abs" := absOfNeg 3 == 3
test "-x.abs" := negOfAbs (-3) == -3
test "-f x" := -addOne 2 == -3
test "a - -b" := (5: Int) - -2 == 7
test "-a * b" := -(2: Int) * 3 == -6
test "Euclidean /" := (7: Int) / -2 == -3
test "ordering" := if h: (-3: Int) < 2 then True else False
test "Nat default" := 3 - 5 == 0
