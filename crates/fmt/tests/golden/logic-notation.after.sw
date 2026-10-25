-- Each spelling stays as written (D1209): the formatter spaces the
-- operators and never converts between ASCII and Unicode.
theorem a (x: Nat) (xs: List Nat): x in xs || x !in xs := ?

theorem b (x: Nat) (xs: List Nat): x ∈ xs ∨ x ∉ xs := ?

theorem c (p: Prop) (q: Prop): p <-> q -> q ↔ p := ?

theorem d: exists (n: Nat) => n * n = 49 := ?

theorem e: ∃ (n: Nat) => n ≤ 7 ∧ n ≠ 3 := ?

def f (seen: List Nat) (x: Nat): Bool := if ¬(x ∈ seen) then !(x in seen) else x !in seen
