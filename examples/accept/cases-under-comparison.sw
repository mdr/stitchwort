-- A comparison of numbers that waits for a value of a finite type: `cases`
-- splits the comparison, which it can't see into, and in the case where
-- that isn't enough it splits the value the comparison's equation still
-- waits for, so the equation computes and contradicts itself (SW-4226).
type Tok = | Plus | Minus | Times | Divide | Less | And

def Tok.level: Tok → Nat
  | Plus => 4
  | Minus => 4
  | Times => 3
  | Divide => 3
  | Less => 2
  | And => 1

theorem levelBelowFive ∀ (tok: Tok): (5 <= tok.level) = False := cases

theorem levelPositive ∀ (tok: Tok): (1 <= tok.level) = True := cases

theorem levelsBelowFive ∀ (a b: Tok): (5 <= a.level || 5 <= b.level) = False := cases
