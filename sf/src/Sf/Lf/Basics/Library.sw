-- Software Foundations, Volume 1: Logical Foundations, Basics.v, the two
-- standard-library lemmas the chapter quotes (`mult_n_O` and `mult_n_Sm`).
-- Copyright and licence: sf/LICENSE-SF.

-- The book's `Check mult_n_O` and `Check mult_n_Sm` show lemmas that come
-- with Rocq, about its own `nat`. The numbers here are the book's own
-- (Sf.Lf.Nat), which has no lemmas, so these two are proved here, for the
-- exercise `multN1` of Basics.sw to use. The proofs are by induction,
-- which the next chapter (Induction.sw) teaches; they use two small
-- facts about `plus` that its exercises ask you to prove, so don't read
-- this file before doing them.

namespace Sf.Lf.Basics.Library
import Sf.Lf.Nat (Nat, plus, mult)
import Std (Eq)

theorem multNO ∀ (n: Nat): O = mult n O := match n with
  | O => rfl
  | S n' => multNO n'

theorem plusSuccR ∀ (n m: Nat): plus n (S m) = S (plus n m) := match n with
  | O => rfl
  | S n' => Eq.cong S (plusSuccR n' m)

theorem plusAssoc ∀ (n m p: Nat): plus n (plus m p) = plus (plus n m) p := match n with
  | O => rfl
  | S n' => Eq.cong S (plusAssoc n' m p)

theorem multNSm ∀ (n m: Nat): plus (mult n m) n = mult n (S m) := match n with
  | O => rfl
  | S n' => rewrite plusSuccR (plus m (mult n' m)) n', <- plusAssoc m (mult n' m) n', multNSm n' m in rfl
