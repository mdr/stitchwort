-- expect-error: E-REFL
-- `t` fails in one case: the error is `t`'s, with a note naming the case by
-- its splits (`a = False, b = False`), and counting the cases closed.
import Std (Bool)

theorem eitherHolds ∀ (a b: Bool): (a || b) = True := cases a, b then byComputing
