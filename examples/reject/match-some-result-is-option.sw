-- expect-error: E-TYPE-MISMATCH
-- Each result of `match some` is wrapped in `Some`: an arm whose result is
-- already an `Option` would make an `Option (Option …)`. Write a `match` there.
import Std (Nat, Option)

def seven: Option Nat := Some 7

def decode: Nat → Option Nat := match some
  | 0 => seven
