-- expect-error: E-CASES
-- SW-3344: `cases` puts a side of an equation it took apart in place of the
-- other only when that side is a variable. `f x = f y` has none, so it stays
-- a fact, shown as `fact 1`, and the goal, which needs it rewritten inside
-- `g`, stays open.
import Std (Nat, Option)

theorem underCall ∀ (f g: Nat → Nat) (x y: Nat) (h: Some (f x) = Some (f y)): g (f x) = g (f y) := cases
