-- Two guards in a row in a proof, each refining the goal where the program
-- tests the same condition, then the arms below both (SW-4388).

def classify (xs: List Nat): Nat := match xs with
  | [x, .._] if x > 10 => 3
  | [x, y, .._] if x == y => 2
  | [_, .._] => 1
  | [] => 0

theorem classifyAtMost ∀ (xs: List Nat): classify xs <= 3 := match xs with
  | [x, .._] if x > 10 => byComputing
  | [x, y, .._] if x == y => byComputing
  | [_, .._] => byComputing
  | [] => byComputing
