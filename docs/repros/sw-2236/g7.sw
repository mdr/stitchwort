import Std (Nat, Bool)

def k (x: Nat): Nat :=
  match x with
    | Zero => 0
    | Succ m => m

def viaHelper (c: Bool) (x: Nat): Nat :=
  match c with
    | True => k x
    | False => 1

def inline (c: Bool) (x: Nat): Nat :=
  match c with
    | True => (match x with
      | Zero => 0
      | Succ m => m)
    | False => 1

theorem atTrue (x: Nat): viaHelper True x = inline True x := rfl

theorem leafAgainstCase (c: Bool) (x: Nat): viaHelper c x = inline c x := rfl
