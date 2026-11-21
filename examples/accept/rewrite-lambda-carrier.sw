-- A rule whose left side is a lambda, with its types left to be found
-- (`etaTwo`'s `a` and `b`), finds them from the lambda it is compared
-- with. A lambda carries no type for its variables, so its type is
-- inferred from how its body uses them and, for one it ignores, from where
-- it sits in the goal: an equation's side or a call's argument (SW-4506).
import Std (Bool, Eq, Nat)

theorem etaTwo ∀ (f: a → a → b): (x y => f x y) = f := byComputing

theorem constOne ∀ (k: b): ((x: a) => k) = ((y: a) => k) := byComputing

-- `a` and `b` from the body: `p` takes two `Nat`s to a `Bool`.
theorem bodyTypes ∀ (p: Nat → Nat → Bool): (x y => p x y) = p := rewrite etaTwo _

-- `c` isn't used: its type `Bool` comes from the equation the lambda is a
-- side of.
theorem sideType: ((c: Bool) => False) = ((d: Bool) => False) := rewrite constOne _

-- Or from the argument of the call it's passed to.
theorem argumentType ∀ (h: (Bool → Bool) → Nat): h ((c: Bool) => False) = h ((d: Bool) => False) := rewrite constOne _

-- A lambda of another type first is passed over: `_` is `p`, not `q`.
theorem otherTypeFirst ∀ (p: Nat → Nat → Bool) (q: Bool → Bool → Nat): (x y => q x y) = q ∧ (x y => p x y) = p :=
  rewrite etaTwo p then (byComputing, byComputing)

theorem holeAtFirst ∀ (p: Nat → Nat → Bool) (q: Bool → Bool → Nat): (x y => q x y) = q ∧ (x y => p x y) = p :=
  rewrite etaTwo _ then (byComputing, byComputing)
