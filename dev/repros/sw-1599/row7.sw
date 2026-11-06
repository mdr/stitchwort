import Std (Abort, List, Nat, Option)

def twice (f: () → {Abort} Nat): {Abort} Nat := f () + f ()

def h1 (o: Option Nat): {Abort} Nat :=
  let k: () → Nat := () => 5
  let a := k ()
  a + twice k

def h2 (o: Option Nat): {Abort} Nat :=
  let k := () => 5
  let a := k ()
  a + 1
