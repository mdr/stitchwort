-- expect-error: E-REFL
-- A type argument is compared, though erased: only proofs are skipped.
-- `f` has no body, so neither side unfolds and only the arguments can
-- decide; a defined function that ignored its type argument would unfold
-- to the same thing on both sides, and that theorem is true.
-- Partner: `sameMod` in accept/proof-irrelevance.sw.
import Std (Bool, Nat)

theorem t2 (f: Type → Nat → Nat) (n: Nat): f Nat n = f Bool n := rfl
