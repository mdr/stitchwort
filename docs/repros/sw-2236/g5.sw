import Std (Nat)

def two (x: Nat): Nat
  decreasing x
:=
  match x with
    | Zero => 2
    | Succ m => two m [decreasing := omega]

def isThree (n: Nat): Nat :=
  match n with
    | 3 => 10
    | _ => 20

theorem plainCase: isThree (Succ 2) = 10 := rfl

theorem topFolded: isThree (two 0) = 20 := rfl

theorem foldedUnderSucc: isThree (Succ (two 0)) = 10 := rfl
