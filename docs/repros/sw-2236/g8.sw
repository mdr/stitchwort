import Std (Nat)

def isThreeA (n: Nat): Nat :=
  match n with
    | 3 => 10
    | _ => 20

def isThreeB (n: Nat): Nat :=
  match n with
    | 3 => 10
    | _ => 20

theorem numCaseTrees (n: Nat): isThreeA n = isThreeB n := rfl
