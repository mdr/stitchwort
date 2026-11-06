-- expect-warning: W-MATCH-DECISION-IF
-- SW-1719: a `match` on a decision refines an `if` only if the `if` still
-- holds the decision, which it does when its branches use the proof of the
-- comparison (`ok` below). Otherwise the `if` is a test of the `Bool` inside
-- the decision, the `match` replaces nothing there, and it warns, whether or
-- not its arms need the refinement. Matching on the condition
-- (`match Nat.leq 10 value with`) refines the `if` in either form.
import Std (Nat, Option, Void)

def below (n: Nat) (limit: Nat) (ok: n < limit): Nat := limit - n

-- The branch uses `ok`, so the `if` keeps the decision: this `match` refines
-- `pos` and doesn't warn.
def gap (n: Nat) (limit: Nat): Nat := if ok: n < limit then below n limit ok else 0

theorem gapPositive (n: Nat) (limit: Nat) (pos: 0 < gap n limit): n < limit :=
  match Nat.decLessThan n limit with
    | Yes lt => lt
    | No _ => omega

-- The branch doesn't use the proof, so the `if` is a `Bool` test: this
-- `match` finds no decision in `pos`. The proof doesn't need `pos` refined, so
-- it passes, with the warning.
def capped (n: Nat) (limit: Nat): Nat := if n < limit then limit - n else 0

theorem cappedSplit (n: Nat) (limit: Nat) (pos: 0 < capped n limit): n < limit ∨ limit ≤ n :=
  match Nat.decLessThan n limit with
    | Yes _ => omega
    | No _ => omega

-- On the condition, the `if` is refined, and there is no warning.
theorem cappedPositive (n: Nat) (limit: Nat) (pos: 0 < capped n limit): n < limit :=
  match Nat.leq (Succ n) limit with
    | True => omega
    | False => omega
