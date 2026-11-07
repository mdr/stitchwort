import Std (Nat)

def pickA (n: Nat) (x: Nat): Nat :=
  match n with
    | Zero => 1
    | Succ k => (match x with
      | Zero => 0
      | Succ m => m)

def pickB (n: Nat) (x: Nat): Nat :=
  match n with
    | Zero => 1
    | Succ k => (match x with
      | Zero => 0
      | Succ m => m)

theorem ctorTrees (x: Nat): pickA (Succ Zero) x = pickB (Succ Zero) x := rfl

theorem numberTrees (x: Nat): pickA 3 x = pickB 3 x := rfl
