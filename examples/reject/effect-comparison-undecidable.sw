-- expect-error: E-AUTO-NONE
-- A comparison whose operand performs an operation is decided where it's
-- passed to a `Bool` parameter. Passed to a parameter of any type, it stays
-- a proposition, which nothing decides where the `Bool` is expected later.
import Std (Bool, Nat, Parse)

def same (x: a): a := x

def short(): {Parse} () := Parse.ensure (same (Parse.mark().offset ≤ 3)) "too long"
