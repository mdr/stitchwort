-- SW-1719, SW-2751: a plain `if` on a decided proposition and an `if h:` are
-- the same term, `Decidable.elim` on the decision, whether or not the
-- branches use the proof. So a `match` on the decision, or on its test,
-- refines the `if` either way, in the goal and in a hypothesis.
import Std (List, Nat, Option, Void)

def below (n: Nat) (limit: Nat) (ok: n < limit): Nat := limit - n

-- The branch uses the proof.
def gap (n: Nat) (limit: Nat): Nat := if ok: n < limit then below n limit ok else 0

theorem gapPositive (n: Nat) (limit: Nat) (pos: 0 < gap n limit): n < limit := match Nat.leq (Succ n) limit with
  | True => rfl
  | False => omega

-- The branch doesn't use the proof.
def capped (n: Nat) (limit: Nat): Nat := if n < limit then limit - n else 0

theorem cappedSplit (n: Nat) (limit: Nat) (pos: 0 < capped n limit): n < limit ∨ limit ≤ n :=
  match Nat.decLessThan n limit with
    | { holds = True, sound = _, complete = _ } => omega
    | { holds = False, sound = _, complete = _ } => omega

theorem cappedPositive (n: Nat) (limit: Nat) (pos: 0 < capped n limit): n < limit := match Nat.leq (Succ n) limit with
  | True => omega
  | False => omega

-- 2021 day 18's `split`: the decision's `False` case refines the `if` in
-- `some` to `None`, which can't be `Some halves`.
type Number =
  | Regular (value: Nat)
  | Pair (left: Number) (right: Number)

def split: Number → Option Number
  | Regular value => if 10 ≤ value then Some (Pair (Regular (value / 2)) (Regular ((value + 1) / 2))) else None
  | Pair _ _ => None

theorem splitBig (value: Nat) (halves: Number) (some: split (Regular value) = Some halves): 10 ≤ value :=
  match Nat.decLessEq 10 value with
    | { holds = True, sound = big, complete = _ } => big rfl
    | { holds = False, sound = _, complete = _ } => Void.exfalso (Option.noneNotSome halves some)

-- `cases` splits the test of `xs = []` inside the decision of `xs ≠ []`,
-- `Decidable.not`, whose own test is `not` of it (2020 day 4's heights).
def allZeroAndNot (xs: List Nat): Bool := (if xs ≠ [] then xs.all (x => x == 0) else False) && False

theorem allZeroAndNotFalse (xs: List Nat): False = allZeroAndNot xs := cases
