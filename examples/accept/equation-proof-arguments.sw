-- A proof that is a plain argument of an equation stays a variable: the
-- equation holds at any proof, not only at `rfl`. (A char pattern's own proof
-- field is `rfl` on the left side instead.)
import Std (Eq, Char)

opaque def pick: (n: Nat) → (p: Char.isScalar n = True) → Option Char
  | 97, p => Some (MkChar 97 p)
  | n, p => None

theorem pickA ∀ (q: Char.isScalar 97 = True): pick 97 q = Some (MkChar 97 q) := pick.eq1 q

def back: (n: Nat) → (p: Char.isScalar n = True) → Char.isScalar n = True
  | 97, p => p
  | n, p => p

theorem backA ∀ (q: Char.isScalar 97 = True): back 97 q = q := back.eq1 q
