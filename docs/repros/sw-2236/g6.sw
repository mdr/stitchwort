import Std (Nat)

def ignoresFirst (a: Nat) (x: Nat): Nat :=
  match x with
    | Zero => 0
    | Succ m => m

def alsoIgnores (a: Nat) (x: Nat): Nat :=
  match x with
    | Zero => 0
    | Succ m => m

theorem otherDef (x: Nat): ignoresFirst 1 x = alsoIgnores 2 x := rfl

theorem sameDef (x: Nat): ignoresFirst 1 x = ignoresFirst 2 x := rfl

theorem middle (x: Nat): alsoIgnores 2 x = ignoresFirst 2 x := rfl
