-- import-rename's proofs, with full names.
namespace Shop.Proofs

theorem emptyAgrees: Shop.total [] = Shop.Spec.total [] := rfl

theorem oneAgrees ∀ (p: Nat): Shop.Spec.total [p] = p + 0 := rfl

theorem sameTotal ∀ (xs: List Nat): Shop.Spec.total xs = Shop.Spec.total xs := rfl
