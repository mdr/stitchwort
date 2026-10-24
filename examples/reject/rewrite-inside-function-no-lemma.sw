-- expect-error: E-REWRITE-CONG
-- `x + 0` uses the variable of the function passed to `total`; rewriting it
-- needs `total`'s congruence lemma, `totalCong`, and there isn't one. The
-- error says what it would say.
import Std (Eq, List, Nat)

def total (f: Nat -> Nat): List Nat -> Nat
  | Nil => 0
  | Cons x xs => f x + total f xs

theorem bad (xs: List Nat): total (x => x + 0) xs = total (x => x) xs :=
  rewrite Nat.addZero _
