-- A comparison as a side of `=` is a proposition; when the other side is a
-- `Bool` (here a `Bool` `&&`), the equation is read again with the
-- comparison as the `Bool` it decides, as if written `((… < k): Bool)`
-- (SW-944; docs/syntax.md, "Anywhere a `Bool` is expected").

import Std (List, Nat)

-- The largest of the start and the numbers is below `k` exactly when each
-- of them is. Before SW-944 this needed `((List.foldLeft … < k): Bool)`.
theorem foldMaxBelow ∀ (k: Nat) (xs: List Nat) (start: Nat):
    (List.foldLeft xs start Nat.max < k) = (start < k ∧ List.all xs (x => x < k)) := match xs with
      | [] => cases
      | [x, ..rest] => rewrite foldMaxBelow k rest (Nat.max start x) in cases

-- The `Bool` on the left is fine as it always was.
theorem withFlag ∀ (b: Bool) (k: Nat): (b ∧ k < 3) = (k < 3 ∧ b) := cases

-- On the right, a comparison beside a `Bool` too.
theorem flagged ∀ (b: Bool) (k: Nat) (h: b = True): (k <= 2) = (b ∧ k < 3) := rewrite h in rfl

-- Two comparisons: an equation between propositions, as before.
theorem sameProp ∀ (k: Nat): (k < 3) = (k < 3) := rfl
