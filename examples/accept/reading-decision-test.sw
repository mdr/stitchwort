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

-- A reading whose proposition is a connective, decided generically by
-- `Decidable.and` from decisions of each side, isn't paired with that
-- decision: `Decidable.and` doesn't choose its test. No warning.
def inRange (lo x hi: Nat): Bool := Nat.leq lo x && Nat.leq x hi

@[reading]
theorem inRangeReads (lo x hi: Nat): inRange lo x hi ↔ lo ≤ x ∧ x ≤ hi :=
  { forward = h => h.read, backward = r => Both r.left r.right }

-- Nor one whose proposition is a relation std decides (`Nat.decLessEq`).
def atMostTen (n: Nat): Bool := Nat.leq n 10

@[reading]
theorem atMostTenReads (n: Nat): atMostTen n ↔ n ≤ 10 := { forward = h => h, backward = h => h }
