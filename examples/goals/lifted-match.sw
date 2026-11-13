-- A `match` inside a definition or a statement is lifted into a helper. A
-- goal stuck on one shows the `match` with what it matches and its
-- alternatives left out, never the helper's internal name (`%match1`).

def Follows (xs: List Nat) (flag: Bool): Prop := match xs with
  | [] => True
  | [x, ..rest] => x ≤ 3 ∧ match flag with
    | True => Follows rest flag
    | False => x = 1

-- The call matched at once; the inner `match` is what the goal is stuck on.
theorem followsCons ∀ (x: Nat) (rest: List Nat) (flag: Bool): Follows [x, ..rest] flag := ?

-- The statement's own `match`.
theorem statementMatch ∀ (flag: Bool) (n: Nat): (match flag with | True => n | False => 0) ≤ n := ?

-- Two scrutinees, shown in the order written.
theorem pairMatch ∀ (a: Nat) (b: Nat): (match a, b with | Zero, _ => 0 | _, Zero => 1 | _, _ => 2) ≤ 2 := ?
