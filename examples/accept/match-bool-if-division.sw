-- SW-1688: an `if` on a comparison whose branches divide. Division is total,
-- so `/` takes no `auto` proof of a nonzero divisor, the branches don't use
-- the comparison's proof, and the `if` is `ifThenElse` on its `Bool`,
-- `Nat.leq 10 value`. A proof follows it with a `match` on that `Bool`, which
-- refines a hypothesis about the call (2021 day 18's `split`). A `match` on
-- the decision `Nat.decLessThan 9 value` would not: the `if` doesn't hold it.
import Std (Eq, Nat, Option, Void)

type Number =
  | Regular (value: Nat)
  | Pair (left: Number) (right: Number)

def split: Number → Option Number
  | Regular value => if 10 ≤ value then Some (Pair (Regular (value / 2)) (Regular ((value + 1) / 2))) else None
  | Pair _ _ => None

theorem splitBig (value: Nat) (halves: Number) (some: split (Regular value) = Some halves): 10 ≤ value :=
  match big: Nat.leq 10 value with
    | True => big
    | False => Void.exfalso (Option.noneNotSome halves some)

theorem splitHalves (value: Nat) (halves: Number) (some: split (Regular value) = Some halves):
    halves = Pair (Regular (value / 2)) (Regular ((value + 1) / 2)) := match Nat.leq 10 value with
      | True => Eq.sym (Option.someInjective some)
      | False => Void.exfalso (Option.noneNotSome halves some)

--| Small numbers don't split, with the proof of `value ≤ 9` from the `False` arm's equation.
theorem smallStays (value: Nat) (none: split (Regular value) = None): value ≤ 9 := match small: Nat.leq 10 value with
  | True => Void.exfalso (Option.someNotNone _ none)
  | False => omega
