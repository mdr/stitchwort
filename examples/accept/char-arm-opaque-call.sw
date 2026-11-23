-- A char-pattern arm whose goal passes the matched character to an opaque
-- call: the arm's `MkChar 97 p` and the literal `'a'` differ only in their
-- proof field, which is equal by rule I (docs/core.md, "Proof
-- irrelevance") wherever it is compared. Was reject/char-arm-opaque-call.sw
-- (E-REFL) before rule I; the second arm's `Eq.cong secret h` was the
-- workaround.
import Std (Eq, Char)

opaque def secret: Char → Nat
  | _ => 3

theorem viaOpaque ∀ (c: Char) (h: c = 'a'): secret c = secret 'a' := match c with
  | 'a' => byComputing
  | _ => Eq.cong secret h
