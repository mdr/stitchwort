-- expect-warning: W-DECISION-TEST
-- A decision of a proposition that a test reads as should test with that
-- test, so `if Small n` and `if isSmall n` are one test, which `rewrite`
-- and `match h:` treat alike (docs/proposals/bool-as-proposition.md §13).
-- `decSmall` tests with another function, equal in what it computes but
-- not the one `isSmallReads` is stated for, so it is warned about.
import Std (Bool, Nat, Iff)

def Small (n: Nat): Prop := n < 10

def isSmall (n: Nat): Bool := Nat.leq (Succ n) 10

@[reading]
theorem isSmallReads (n: Nat): isSmall n ↔ Small n := { forward = h => h, backward = h => h }

def smallTest (n: Nat): Bool := Nat.leq (Succ n) 10

instance decSmall (n: Nat): Decidable (Small n) := { holds = smallTest n, sound = h => h, complete = h => h }

-- Written with the test that reads as it: no warning.
def Big (n: Nat): Prop := 10 < n

def isBig (n: Nat): Bool := Nat.leq 11 n

@[reading]
theorem isBigReads (n: Nat): isBig n ↔ Big n := { forward = h => h, backward = h => h }

instance decBig (n: Nat): Decidable (Big n) :=
  { holds = isBig n, sound = (isBigReads n).forward, complete = (isBigReads n).backward }
