-- SW-3055: dividing a number with a huge constant added to an unknown, as in
-- `(value + 2^128) / 2`, takes the divisor's steps off the constant at once
-- (`Nat.divFuel`'s native), where one `Succ` at a time was 2^127 steps and
-- gigabytes. Checking a proof about the call must stay instant.
import Std (Nat, Option, Void)

type Number = | Regular (value: Nat) | Pair (left: Number) (right: Number)

def split: Number → Option Number
  | Regular value =>
    if 10 ≤ value then
      Some (Pair (Regular (value / 2)) (Regular ((value + 340282366920938463463374607431768211456) / 2)))
    else None
  | Pair _ _ => None

theorem splitBig ∀ (value: Nat) (halves: Number) (some: split (Regular value) = Some halves): 10 ≤ value :=
  match big: Nat.leq 10 value with
    | True => big
    | False => Void.exfalso (Option.noneNotSome halves some)
