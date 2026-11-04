-- expect-error: E-REFL
-- A proposition parameter is a type, so it's compared: only proofs of
-- propositions are skipped. Partner: `sameProposition` in
-- accept/proof-irrelevance.sw.
import Std (Unit, Void)

type R (p: Prop): Type =
  | MkR

theorem t9: R Unit = R Void := rfl
