-- SW-1719, after `Decidable` became a record (SW-2746): a `match` on an
-- `if`'s condition (`match Nat.leq (Succ n) limit with`) refines the `if`
-- whether or not its branches use the proof of the comparison. With the
-- proof used (`ok` below), the `if` decides `n < limit`, whose decision's
-- test is that condition; without it, the `if` is a test of the condition
-- itself.
import Std (Nat, Option, Void)

def below (n: Nat) (limit: Nat) (ok: n < limit): Nat := limit - n

-- The branch uses `ok`, so the `if` keeps the decision, `Nat.decLessThan n
-- limit`, whose test is `Nat.leq (Succ n) limit`.
def gap (n: Nat) (limit: Nat): Nat := if ok: n < limit then below n limit ok else 0

theorem gapPositive (n: Nat) (limit: Nat) (pos: 0 < gap n limit): n < limit :=
  match Nat.leq (Succ n) limit with
    | True => rfl
    | False => omega

-- The branch doesn't use the proof, so the `if` is a `Bool` test.
def capped (n: Nat) (limit: Nat): Nat := if n < limit then limit - n else 0

theorem cappedPositive (n: Nat) (limit: Nat) (pos: 0 < capped n limit): n < limit :=
  match Nat.leq (Succ n) limit with
    | True => omega
    | False => omega
