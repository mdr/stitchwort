import Std (Nat)

def two (x: Nat): Nat
    decreasing x
:=
  match x with
    | Zero => 2
    | Succ m => two m [decreasing := omega]

theorem plainSum (x: Nat): x + 2 = Succ (Succ x) := rfl

theorem foldedSum (x: Nat): x + two 0 = Succ (Succ x) := rfl

def isPos (n: Nat): Nat :=
  match n with
    | Zero => 0
    | Succ _ => 1

def isZero (n: Nat): Bool :=
  match n with
    | 0 => True
    | _ => False

-- A `case` and a number `match` read the sum too.
theorem foldedSumMatched (x: Nat): isPos (x + two 0) = 1 := rfl

theorem foldedSumNumberMatched (x: Nat): isZero (x + two 0) = False := rfl
