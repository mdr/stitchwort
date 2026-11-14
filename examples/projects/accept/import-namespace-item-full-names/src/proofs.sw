-- `Shop.Spec.total`, written in full.
namespace Shop.Proofs

import Shop (total)

theorem emptyAgrees: total [] = Shop.Spec.total [] := rfl

theorem oneAgrees ∀ (p: Nat): Shop.Spec.total [p] = p + 0 := rfl
