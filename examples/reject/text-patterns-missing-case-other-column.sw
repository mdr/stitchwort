-- expect-error: E-NONEXHAUSTIVE
-- The texts no arm lists are missing only where the other column is `True`:
-- the message names that case.
def pick: Bool → Text → Nat
  | True, "a" => 1
  | True, "b" => 2
  | False, _ => 3
