-- A definition and a namespace imported under other names. Neither
-- `total` nor `Spec` is brought by these items.
namespace Shop.Proofs

import Shop (Spec as S, total as charged)
import Shop.Spec (total as specified)

theorem emptyAgrees: charged [] = S.total [] := rfl

theorem oneAgrees ∀ (p: Nat): specified [p] = p + 0 := rfl

-- Two names in this file for `Shop.Spec.total`.
theorem sameTotal ∀ (xs: List Nat): specified xs = S.total xs := rfl
