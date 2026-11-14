import Std (Abort, List, Nat, Option)

def a1 (xs: List (Option Nat)): {Abort} Nat := xs.foldLeft 0 (acc o => acc + Abort.need o)

def a2 (xs: List (Option Nat)): {Abort} List Nat := xs.foldLeft [] (acc o => [Abort.need o, ..acc])

def step (acc: Nat) (o: Option Nat): {Abort} Nat := acc + Abort.need o

def a3 (xs: List (Option Nat)): {Abort} Nat := xs.foldLeft 0 step

def a4 (xs: List (Option Nat)): {Abort} Nat :=
  let f := step
  xs.foldLeft 0 f

def a5 (xs: List (Option Nat)): {Abort} Nat := xs.foldLeft 0 (acc o =>
  match o with
    | Some n => acc + n
    | None => Abort.need None)
