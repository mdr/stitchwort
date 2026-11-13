-- SW-2828: `rewrite` carries a decision's proofs along the equation where
-- the usual motive fails (crates/elab/src/carry.rs). `Nat.decEq`'s proofs are
-- lambdas, `h => Nat.equalSound m n h`, and the kernel can't infer a
-- lambda's type, so they are applied to the carried proof by a `let` rather
-- than by a call, which wouldn't check.
import Std (Bool, Eq, Nat)

theorem ifEqualOne ∀ (m: Nat) (n: Nat) (h: Nat.equal m n = True): (if m = n then 1 else 0) = 1 :=
  rewrite h in rfl
