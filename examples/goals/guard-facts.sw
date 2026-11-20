-- An arm under an unnamed guard lists the guard's fact as a line under the
-- context, in the arm's names, as a catch-all's facts are listed: the
-- guard's test is `True` in the arm (printed bare, `c == '('`) and `False`
-- in the arms below, and a proposition guard `P` gives `P` and `¬P`. A named guard shows as its name.
import Std (Bool, Char, Nat)

theorem characters ∀ (p: Char → Prop) (c: Char): p c := match c with
  | c if c == '(' => ?
  | c if c == ')' => ?
  | c => ?

theorem propositions ∀ (p: Nat → Prop) (n: Nat): p n := match n with
  | n if n < 3 => ?
  | n => ?

theorem named ∀ (p: Nat → Prop) (n: Nat): p n := match n with
  | n if g: n == 0 => ?
  | n => ?
