import Std (Abort, List, Nat, Option)

def twice (f: () → {Abort} Nat): {Abort} Nat := f () + f ()

def f1 (o: Option Nat): {Abort} Nat :=
  let k := () => 5
  let a := k ()
  twice k

def f2 (o: Option Nat): {Abort} Nat :=
  let k := () => 5
  twice k + k ()
