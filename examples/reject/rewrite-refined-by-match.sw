-- expect-error: E-REWRITE-NOTHING
-- Inside `match c: isBig n`, the goal and every hypothesis mentioning
-- `isBig n` have it replaced by the branch's constructor, so `found` has no
-- `isBig n` left to rewrite: the error says the `match` replaced it.
import Std (Option, Void)

def isBig (n: Nat): Bool := 10 < n

def pick (n: Nat): Option Nat := if isBig n then None else Some n

theorem pickSmall (n: Nat) (m: Nat) (found: pick n = Some m): n = m :=
  match c: isBig n with
    | True => Void.exfalso (Option.noneNotSome m found)
    | False => Option.someInjective _ _ (rewrite c at found)
