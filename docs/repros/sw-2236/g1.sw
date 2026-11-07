import Std (Nat, Bool)

def yes (x: Nat): Bool
  decreasing x
:=
  match x with
    | Zero => True
    | Succ m => yes m [decreasing := omega]

def pickA (b: Bool) (x: Nat): Nat :=
  match b with
    | True => (match x with
      | Zero => 0
      | Succ m => m)
    | False => 1

def pickB (b: Bool) (x: Nat): Nat :=
  match b with
    | True => (match x with
      | Zero => 0
      | Succ m => m)
    | False => 1

theorem plainTrees (x: Nat): pickA True x = pickB True x := rfl

theorem foldedTrees (x: Nat): pickA (yes 0) x = pickB (yes 0) x := rfl
