-- expect-error: E-UNFOLDING-TRANSPARENT
-- A definition that unfolds an opaque one must be opaque itself: a
-- transparent one unfolds everywhere, and would carry the body it used to
-- places where that body is hidden. (docs/proposals/opaque-definitions.md
-- §6.3.)
import Std (Nat)

opaque def double (n: Nat): Nat := n + n

def quadruple (n: Nat): Nat unfolding double := double (double n)
