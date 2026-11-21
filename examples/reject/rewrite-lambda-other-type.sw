-- expect-error: E-REWRITE-NOTHING
-- The rule's left side is a function of a `Nat`; the goal's only lambda
-- takes a `Bool`, so it isn't an occurrence, though both ignore their
-- variable (SW-4506).
import Std (Bool, Eq, Nat)

theorem constNat ∀ (k: Bool): ((x: Nat) => k) = ((y: Nat) => k) := byComputing

theorem otherType ∀ (h: (Bool → Bool) → Nat): h ((c: Bool) => False) = h ((d: Bool) => True) := rewrite constNat _
