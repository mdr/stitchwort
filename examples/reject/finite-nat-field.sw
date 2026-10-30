-- expect-error: E-INSTANCE-NONE
-- `Finite` isn't derived for a type with a field of a type that has no
-- `Finite` instance, here `Nat` (docs/proposals/decide.md §6.2). The error
-- names the field.
import Std (List)

type Reading =
  | Missing
  | Count (n: Nat)

def readings: List Reading := Finite.all
