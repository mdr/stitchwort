-- expect-error: E-MATCH-SIZE
-- Each guarded arm that splits another column copies the arms below it, so
-- thirteen of them would make thousands of copies.

def many: Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat
  | 0, _, _, _, _, _, _, _, _, _, _, _, _ if False => 1
  | _, 0, _, _, _, _, _, _, _, _, _, _, _ if False => 1
  | _, _, 0, _, _, _, _, _, _, _, _, _, _ if False => 1
  | _, _, _, 0, _, _, _, _, _, _, _, _, _ if False => 1
  | _, _, _, _, 0, _, _, _, _, _, _, _, _ if False => 1
  | _, _, _, _, _, 0, _, _, _, _, _, _, _ if False => 1
  | _, _, _, _, _, _, 0, _, _, _, _, _, _ if False => 1
  | _, _, _, _, _, _, _, 0, _, _, _, _, _ if False => 1
  | _, _, _, _, _, _, _, _, 0, _, _, _, _ if False => 1
  | _, _, _, _, _, _, _, _, _, 0, _, _, _ if False => 1
  | _, _, _, _, _, _, _, _, _, _, 0, _, _ if False => 1
  | _, _, _, _, _, _, _, _, _, _, _, 0, _ if False => 1
  | _, _, _, _, _, _, _, _, _, _, _, _, 0 if False => 1
  | _, _, _, _, _, _, _, _, _, _, _, _, _ => 2
