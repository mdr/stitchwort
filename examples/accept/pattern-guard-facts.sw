-- What a guarded arm knows (docs/proposals/pattern-guards.md §4): the
-- arm knows its condition, as the branch of an `if` does, and the arms below
-- it know it failed.

-- `len % n` needs `n ≠ 0`, which the condition gives.
def remainder: (Nat, Nat) → Nat
  | (n, len) if n != 0 => len % n
  | _ => 0

test "remainder" := remainder (3, 10) == 1 ∧ remainder (0, 10) == 0

-- A function that asks for a proof is called with the arm's fact.
def needsPositive (n: Nat) [auto h: n > 0]: Nat := n - 1

def predecessor: Nat → Nat
  | n if n > 0 => needsPositive n
  | _ => 0

test "predecessor" := predecessor 5 == 4 ∧ predecessor 0 == 0

-- `if h: P` names the fact in the arm.
def predecessorNamed: Nat → Nat
  | n if h: n > 0 => needsPositive n
  | _ => 0

test "named" := predecessorNamed 5 == 4 ∧ predecessorNamed 0 == 0
