-- expect-error: E-REFL
-- An indexed proposition whose constructor has a field is outside rule S
-- (D3724 follows Lean, which computes such a match only with no fields): a
-- match on an unknown proof of it into data stays stuck, even at indices
-- that agree.
import Std (Nat)

type Le2: Nat → Prop = | MkLe2 (p: 0 = 0): Le2 0

def withField (n: Nat) (h: Le2 n) (k: Nat): Nat := match h with | MkLe2 p => k

theorem fieldStuck ∀ (h: Le2 0): withField 0 h 4 = 4 := byComputing
