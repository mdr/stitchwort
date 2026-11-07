-- D2307: parentheses around the type after an ability row are redundant.
def applied: {Fail} (List Nat) := []
def named: {Fail} (Nat) := 0
def tupleArg: {Parse} (Option (Nat, Nat)) := None
def tupleNested: {Fail} ((Nat, Nat)) := (0, 0)
-- Kept: a function type reads better with them; these change the parse, or
-- hold a tuple or unit.
def arrowType: {e} (Nat -> Nat) := id
def nested: {e} ((Nat -> Nat) -> Nat) := id
def dependent: {e} ((y: Nat) -> Nat) := id
def keepDomain: {e} (Nat -> Nat) -> Nat := id
def keepTuple: {Fail} (Nat, Nat) := (0, 0)
def keepUnit: {IO} () := ()
