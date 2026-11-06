import Std (Abort, List, Nat, Option)

def twice (f: () → {Abort} Nat): {Abort} Nat := f () + f ()

def c1 (o: Option Nat): {Abort} Nat :=
  let k := () => 5
  let a := k ()
  a + twice k + Abort.need o

def c2 (o: Option Nat): {Abort} Nat :=
  let k := () => Abort.need o
  let a := k ()
  a + twice k
