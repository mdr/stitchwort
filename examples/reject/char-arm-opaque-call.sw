-- expect-error: E-REFL
-- A char-pattern arm whose goal passes the matched character to an opaque
-- call: the arm's `MkChar 97 p` and the literal `'a'` differ in their proof
-- field, which a comparison under an opaque call doesn't skip (D2352), so
-- `rfl` is refused. Workaround: `Eq.cong secret h`, as in the second arm.
import Std (Eq, Char)

opaque def secret: Char → Nat
  | _ => 3

theorem viaOpaque ∀ (c: Char) (h: c = 'a'): secret c = secret 'a' := match c with
  | 'a' => rfl
  | _ => Eq.cong secret h
