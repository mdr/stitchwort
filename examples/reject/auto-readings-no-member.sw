-- expect-error: E-AUTO-STUCK
-- `xs.all p = True` reads as `∀ (x: Nat) => x ∈ xs → p x`, which `auto`
-- applies only to a member it can see: here nothing says `y ∈ xs`.
import Std (List, Nat)

def small (x: Nat) [auto ok: x < 5]: Nat := x

def unknownMember (xs: List Nat) (y: Nat) (h: xs.all (x => x < 5) = True): Nat := small y
