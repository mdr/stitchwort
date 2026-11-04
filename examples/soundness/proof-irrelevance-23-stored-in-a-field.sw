-- expect-error: E-REFL
-- A proof stored in a constructor field isn't inert (D2354), so the
-- shortcut compares it, and the unfoldings are `p` and `q`. Partner:
-- `keepBoth` in accept/proof-irrelevance.sw.
import Std (Nat)

type Box (a: Prop): Type =
  | MkBox (h: a)

def Box.unbox [a: Prop]: Box a → a
  | MkBox h => h

def keep (d: Nat) (ok: d ≠ 0): Box (d ≠ 0) := MkBox ok

theorem t23 (d: Nat) (p: d ≠ 0) (q: d ≠ 0): Box.unbox (keep d p) = Box.unbox (keep d q) := rfl
