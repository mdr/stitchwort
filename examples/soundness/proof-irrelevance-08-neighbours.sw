-- expect-error: E-REFL
-- Skipping a proof field doesn't skip its neighbours. Partner:
-- `sortedLists` in accept/proof-irrelevance.sw.
import Std (Nat)

type Checked: Type =
  | MkChecked (n: Nat) (ok: n = n)

theorem t8 (x: Nat) (y: Nat): MkChecked x rfl = MkChecked y rfl := rfl
