-- expect-error: E-CASES
-- Against the goal `every (flip xs) p = True`, `headLe`'s conclusion `?le
-- ?x ?z = True` isn't a pattern, and matching the last arguments would pair
-- `?z` with `p` and `?x` with `flip xs`, though both have `headLe`'s one
-- type `a`, and solve `?le` with `every`. The heads' types say `a` is `p`'s
-- type, so `flip xs`, a list, isn't paired: `cases` is checked against an
-- unknown `le` and finds nothing to split (SW-4564: it was checked against
-- `every` applied to a list where `p` goes, split it, and core crashed
-- applying a constructor).
def every (xs: List a) (p: a → Bool): Bool := match xs with
  | [] => True
  | [x, ..rest] => p x && every rest p

def flip (xs: List a): List a := match xs with
  | [] => []
  | [x, ..rest] => [x, ..rest]

theorem headLe ∀ (le: a → a → Bool)
    (trans: ∀ (x y z: a) => le x y = True → le y z = True → le x z = True) (x z: a)
    (h: le x z = True):
    le x z = True :=
  h

theorem t ∀ (p: a → Bool) (xs: List a): every (flip xs) p = True := headLe _ cases _ _ ?
