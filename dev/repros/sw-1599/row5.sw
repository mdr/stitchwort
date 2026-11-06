import Std (Abort, List, Nat, Option)

def twice (f: () → {Abort} Nat): {Abort} Nat := f () + f ()

def e1 (o: Option Nat): {Abort} Nat :=
  let k: () → Nat := () => 5
  twice k

def e2 (o: Option Nat): {Abort} Nat :=
  let k := () => 5
  twice k
