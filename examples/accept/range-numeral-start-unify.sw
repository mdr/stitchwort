-- A range with a numeral start and a computed end: the hypothesis's type
-- evaluates to `List.rangeFrom (n - 1) 2`, and the lemma's `List.range ?a ?b`
-- must be matched against it without guessing `?b - ?a` from `n - 1`.
import Std (List, Nat)

theorem fromRange ∀ (n x: Nat) (h: x ∈ List.range 2 (n + 1)): 2 ≤ x :=
  And.left ((List.memRange _ _ _).forward h)

theorem fromOperator ∀ (n x: Nat) (h: x ∈ 2 ..= n): 2 ≤ x :=
  And.left ((List.memRange _ _ _).forward h)

theorem fromHalfOpen ∀ (n x: Nat) (h: x ∈ 3 ..< n + 2): 3 ≤ x :=
  And.left ((List.memRange _ _ _).forward h)

theorem intoRange ∀ (n x: Nat) (lo: 2 ≤ x) (hi: x < n + 1): x ∈ List.range 2 (n + 1) :=
  (List.memRange _ _ _).backward (Both lo hi)

theorem intoClosed ∀ (n x: Nat) (lo: 2 ≤ x) (hi: x ≤ n): x ∈ 2 ..= n :=
  (List.memRange _ _ _).backward (Both lo (omega))

theorem intoHalfOpen ∀ (n x: Nat) (lo: 3 ≤ x) (hi: x < n + 2): x ∈ 3 ..< n + 2 :=
  (List.memRange _ _ _).backward (Both lo hi)
