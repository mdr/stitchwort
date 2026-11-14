-- Integers, extracted to JS (docs/proposals/integers.md): an `Int` is a
-- `bigint` of either sign at the boundary and inside generated code. Every
-- division is total (`x / 0 = 0`, `x % 0 = x`); an export can still ask for a
-- divisor that isn't 0, a precondition checked at runtime.
--
-- run: dial (-18)
-- run: divide (-7) 2
-- run: divide 7 (-2)
-- rejects: divide (OfNat 5) (OfNat 0)
-- run: describe (-1)
-- run: describe 0
-- run: describe 1000000000000000000000000000000
-- run: negatives [0, 4]

import Std (Decidable, Int, List, Nat, Option, Text)

-- Where a dial at 0 ends up after `x` clicks, on a dial of 100.
export def dial (x: Int): Int := x % 100

-- Each of the three conventions, and a precondition checked in JS.
export def divide (a d: Int): [auto ok: d ≠ 0] → List Int :=
  [a / d, a % d, Int.tdiv a d, Int.tmod a d, Int.fdiv a d, Int.fmod a d]

export def describe: Int → Text
  | 0 => "zero"
  | (-1) => "minus one"
  | x => if Int.less x 0 then "negative" else "positive"

export def negatives (ns: List Nat): List Int := List.map ns NegSucc

-- Every natively implemented operation, one export each.
export def neg (x: Int): Int := -x

export def add (a b: Int): Int := a + b

export def sub (a b: Int): Int := a - b

export def mul (a b: Int): Int := a * b

export def eucDiv (a d: Int): Int := a / d

export def eucMod (a d: Int): Int := a % d

export def tdiv (a d: Int): Int := Int.tdiv a d

export def tmod (a d: Int): Int := Int.tmod a d

export def fdiv (a d: Int): Int := Int.fdiv a d

export def fmod (a d: Int): Int := Int.fmod a d

export def modNat (a: Int) (d: Nat): Nat := Int.modNat a d

export def natDivMod (n d: Nat): List Nat := [n / d, n % d]

export def decEq (a b: Int): Bool := Decidable.holds (Int.decEq a b)

export def leq (a b: Int): Bool := Int.leq a b

export def less (a b: Int): Bool := Int.less a b

export def compare (a b: Int): Ordering := Int.compare a b

export def natAbs (x: Int): Nat := Int.natAbs x

export def abs (x: Int): Int := Int.abs x

export def toNat (x: Int): Nat := Int.toNat x

export def toNatChecked (x: Int): Option Nat := Int.toNatChecked x

export def sign (x: Int): Int := Int.sign x

export def ofNat (n: Nat): Int := Nat.toInt n

export def toText (x: Int): Text := Int.toText x

export def parse (t: Text): Option Int := Text.toInt t

-- run: neg 5
-- run: neg (-5)
-- run: add (-3) 10
-- run: sub 3 10
-- run: mul (-4) 5
-- run: eucDiv (-7) 2
-- run: eucMod (-7) (-2)
-- run: tdiv (-7) 2
-- run: tmod (-7) 2
-- run: fdiv 7 (-2)
-- run: fmod 7 (-2)
-- run: modNat (-7) 3
-- run: eucDiv 5 0
-- run: eucMod (-5) 0
-- run: tdiv 5 0
-- run: tmod (-5) 0
-- run: fdiv (-5) 0
-- run: fmod 5 0
-- run: modNat (-5) 0
-- run: modNat 5 0
-- run: natDivMod 7 0
-- run: natDivMod 7 2
-- run: decEq 5 5
-- run: decEq 5 (-5)
-- run: leq (-5) (-5)
-- run: less (-5) (-5)
-- run: less (-6) (-5)
-- run: compare (-1) 0
-- run: compare 0 0
-- run: compare 1 0
-- run: natAbs (-5)
-- run: abs (-5)
-- run: toNat (-5)
-- run: toNat 5
-- run: toNatChecked (-5)
-- run: toNatChecked 5
-- run: sign (-5)
-- run: sign 0
-- run: sign 5
-- run: ofNat 5
-- run: toText (-5)
-- run: toText 1000000000000000000000000000000
-- run: parse "-12"
-- run: parse "007"
-- run: parse "+5"
-- run: parse ""
-- run: parse "-"

-- User code through the representation: constructors as values, patterns on
-- native results, and an `Int` pattern of each shape.
export def ofNats (ns: List Nat): List Int := List.map ns OfNat

export def residue (a d: Int): [auto ok: d ≠ 0] → Text := residueName (a % d)

def residueName: Int → Text
  | 0 => "zero"
  | 1 => "one"
  | (-1) => "minus one"
  | r => if Int.less r 0 then "negative" else "other"

export def classify: Int → Text
  | 0 => "zero"
  | 1 => "one"
  | (-1) => "minus one"
  | 1000000000000000000000000000000 => "10^30"
  | (-1000000000000000000000000000000) => "-10^30"
  | OfNat 2 => "two"
  | NegSucc 1 => "minus two"
  | OfNat k => "positive or zero, k = " ++ Nat.toText k
  | NegSucc k => "negative, k = " ++ Nat.toText k

-- Both constructor patterns, with the field used.
export def fields: Int → Nat
  | OfNat k => k
  | NegSucc k => k + 100

export def optionInt: Option Int → Int
  | None => 0
  | Some x => x * 2

export def negateAll (xs: List (Option Int)): List (Option Int) := List.map xs (m => Option.map m Int.neg)

export def firstNeg: List Int → Option Int
  | Nil => None
  | Cons x xs => if Int.less x 0 then Some x else firstNeg xs

type Entry = { count: Nat, delta: Int }

export def apply (e: Entry): Entry := { e | delta = e.delta + OfNat e.count }

export def entries: List Entry → Int
  | Nil => 0
  | Cons e es => e.delta + entries es

-- run: ofNats [1, 2]
-- run: ofNats []
-- run: negatives [0, 4]
-- run: residue 7 2
-- run: residue (-7) 2
-- run: residue 6 2
-- run: residue (-6) 4
-- run: residue 5 (-2)
-- run: classify 0
-- run: classify 1
-- run: classify (-1)
-- run: classify 2
-- run: classify (-2)
-- run: classify 1000000000000000000000000000000
-- run: classify (-1000000000000000000000000000000)
-- run: classify 77
-- run: classify (-77)
-- run: fields 5
-- run: fields (-5)
-- run: optionInt None
-- run: optionInt (Some (-4))
-- run: negateAll [None, Some 3, Some (-3)]
-- run: firstNeg [3, -4, -5]
-- run: firstNeg [3]
-- run: apply { count = 3, delta = -10 }
-- run: entries [{ count = 1, delta = -5 }, { count = 2, delta = 7 }]
