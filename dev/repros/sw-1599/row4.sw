import Std (Abort, List, Nat, Option)

def twice (f: () → {Abort} Nat): {Abort} Nat := f () + f ()

def d1 (o: Option Nat): {Abort} Nat :=
  let k := () => 5
  twice k + Abort.need o

def d2 (o: Option Nat): {Abort} Nat :=
  let k := () => 5
  let a := k ()
  a + Abort.need o

def d3 (o: Option Nat): {Abort} Nat :=
  let k := () => 5
  let a := k ()
  a + twice k
