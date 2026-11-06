import Std (Abort, List, Nat, Option)

def twice (f: () → {Abort} Nat): {Abort} Nat := f () + f ()

def poly (): {e} Nat := 5

def i1 (o: Option Nat): {Abort} Nat :=
  let k := () => poly ()
  let a := k ()
  a + twice k
