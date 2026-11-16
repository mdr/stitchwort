-- expect-error: E-TYPE-MISMATCH
-- A plain implicit parameter whose type is an interface is solved only by
-- unification, never by instance search, so `add` stays unknown here and the
-- message says to write `[auto add: Add a]` to have the instance found.

import Std (List, Add)

theorem sumCong [a: Type] [add: Add a] (xs: List a) (f: a → a) (g: a → a) (same: f = g):
    xs.sumBy f = xs.sumBy g := rewrite same then byComputing

def idI (x: Int): Int := x
def idI2 (x: Int): Int := x
theorem fnSame: idI = idI2 := byComputing

theorem use ∀ (xs: List Int): xs.sumBy idI = xs.sumBy idI2 := sumCong xs idI idI2 fnSame
