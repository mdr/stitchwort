import Std (Abort, List, Nat, Option)

type Tally = { total: Nat }

def b1 (xs: List (Option Nat)): {Abort} Tally :=
  xs.foldLeft { total = 0 } (acc o => { total = acc.total + Abort.need o })

def addNeed (acc: Tally) (o: Option Nat): {Abort} Tally := { total = acc.total + Abort.need o }

def b2 (xs: List (Option Nat)): {Abort} Tally := xs.foldLeft { total = 0 } addNeed

def b3 (xs: List (Option Nat)): {Abort} Nat :=
  let t := xs.foldLeft { total = 0 } addNeed
  t.total

def b4 (xs: List (Option Nat)): {Abort} Nat := List.foldLeft xs 0 (acc o => acc + Abort.need o)

def b5 (xs: List (Option Nat)): {Abort} Nat :=
  let step := (acc: Nat) => (o: Option Nat) => acc + Abort.need o
  xs.foldLeft 0 step
