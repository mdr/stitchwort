-- `Spec.total` is `Shop.Spec.total`: the import brings the qualifier
-- `Spec`, and none of the names in it.
namespace Shop.Proofs

import Shop (Spec, total)

theorem emptyAgrees: total [] = Spec.total [] := rfl

theorem oneAgrees ∀ (p: Nat): Spec.total [p] = p + 0 := rfl
