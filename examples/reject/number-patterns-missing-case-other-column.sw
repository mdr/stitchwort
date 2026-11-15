-- expect-error: E-NONEXHAUSTIVE
-- The numbers no arm lists are missing only where the other column is
-- `Some _`: the message names that case.
def pick: Option Bool → Nat → Nat
  | Some _, 0 => 1
  | Some _, 1 => 2
  | None, _ => 3
