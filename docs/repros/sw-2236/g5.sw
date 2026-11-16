import Std (Nat)

def two (x: Nat): Nat
  decreasing x
:=
  match x with
    | Zero => 2
    | Succ m => two m [decreasing := arithmetic]

def isThree (n: Nat): Nat :=
  match n with
    | 3 => 10
    | _ => 20

theorem plainCase: isThree (Succ 2) = 10 := byComputing

theorem topFolded: isThree (two 0) = 20 := byComputing

theorem foldedUnderSucc: isThree (Succ (two 0)) = 10 := byComputing
