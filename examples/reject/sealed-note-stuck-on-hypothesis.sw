-- expect-error: E-TYPE-MISMATCH
-- The cast is stuck on the hypothesis `h`, through `h.left`, not on
-- `And.left` being a theorem: unsealing it wouldn't help, so the error
-- doesn't say the proof is sealed. (A theorem called on closed arguments
-- does: `sealed-theorem-cast`.)
import Std (Nat, Eq)

def pick (a b n: Nat): Nat := if h: (a = b) ∧ (b = 0) then J (x e => Nat) n h.left else 0

theorem pickEq ∀ (a b n: Nat) (h: (a = b) ∧ (b = 0)): pick a b n = n := pick.eq.ifTrue a b n h
