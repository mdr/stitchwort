-- Building a test fact from a proof of its reading never changes a program
-- that checks without it: the build is only tried once a declaration has
-- failed (docs/proposals/bool-as-proposition-building.md §2.4, §3).
import Std (Bool, Eq, List, Nat)

type Checked (p: Prop) = { item: Nat, why: p }

-- The update changes the record's parameter to `x ∈ xs`, as it did before
-- building existed; the next line relies on that.
def recheck (x: Nat) (xs: List Nat) (c: Checked (xs.contains x = True)) (m: x ∈ xs): Nat :=
  let again := { c | why = m }
  let member: x ∈ xs := again.why
  again.item

-- A test fact used as the equation it is stays one between `Bool`s.
theorem flipped ∀ (x y: Nat) (same: (x == y) = True): True = (x == y) := Eq.sym same

theorem rewritten ∀ (x y: Nat) (same: (x == y) = True): (if x == y then 1 else 2) = 1 :=
  rewrite same in rfl
