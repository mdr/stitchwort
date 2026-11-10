-- expect-warning: W-MATCH-DECISION-IF
-- SW-1719: a `match` on a decision refines an `if` only if the `if` still
-- holds the decision. An `if` whose branches don't use the proof of its
-- comparison is a test of the decision's `Bool`, the `match` replaces nothing
-- there, and it warns, whether or not its arms need the refinement. Matching
-- on the condition (`match Nat.leq (Succ n) limit with`) refines the `if`
-- whether or not its branches use the proof.
import Std (Nat)

def below (n: Nat) (limit: Nat) (ok: n < limit): Nat := limit - n

-- The branch uses `ok`, so the `if` decides `n < limit` with
-- `Nat.decLessThan n limit`, whose test is the condition matched on.
def gap (n: Nat) (limit: Nat): Nat := if ok: n < limit then below n limit ok else 0

theorem gapPositive (n: Nat) (limit: Nat) (pos: 0 < gap n limit): n < limit :=
  match Nat.leq (Succ n) limit with
    | True => rfl
    | False => omega

-- The branch doesn't use the proof, so the `if` is a `Bool` test: this
-- `match` finds no decision in `pos`. The proof doesn't need `pos` refined, so
-- it passes, with the warning.
def capped (n: Nat) (limit: Nat): Nat := if n < limit then limit - n else 0

theorem cappedSplit (n: Nat) (limit: Nat) (pos: 0 < capped n limit): n < limit ∨ limit ≤ n :=
  match Nat.decLessThan n limit with
    | { holds = True, sound = _, complete = _ } => omega
    | { holds = False, sound = _, complete = _ } => omega

-- On the condition, the `if` is refined, and there is no warning.
theorem cappedPositive (n: Nat) (limit: Nat) (pos: 0 < capped n limit): n < limit :=
  match Nat.leq (Succ n) limit with
    | True => omega
    | False => omega
