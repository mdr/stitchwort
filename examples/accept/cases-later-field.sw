-- SW-975: `cases` takes a hypothesis `C a1 … = C b1 …` apart into one
-- equation per field, each at that field's type. A later field's type is
-- read under the parameters and the earlier fields: read under the
-- parameters alone, a pair's second field got the first's type, so `p = q`
-- below was built at `Nat` (a type mismatch) or `Bool` (not the goal).
import Std (Bool, List, Nat, Pair)

theorem sndEqual ∀ (x: Nat) (p: Bool) (y: Nat) (q: Bool) (h: (x, p) = (y, q)): p = q := cases

theorem sndEqualSwapped ∀ (x: Bool) (p: Nat) (y: Bool) (q: Nat) (h: (x, p) = (y, q)): p = q := cases

theorem tailEqual ∀ (x: Nat) (xs: List Nat) (y: Nat) (ys: List Nat) (h: [x, ..xs] = [y, ..ys]): xs = ys := cases
