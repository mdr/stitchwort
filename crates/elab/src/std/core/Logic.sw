-- core/Logic.sw. `Void`, `Unit`, `Not`, `And`, `Or`, and `absurd`/`exfalso`.
-- Loaded with the core: every proof the core states is built from these, and
-- `Decidable`, `deriving` and `auto` write them in full
-- (docs/proposals/prelude-slim.md §2.1).

-- Logic

-- The proposition with no proofs: false.
type Void: Prop

-- The proposition with exactly one proof: true.
type Unit: Prop =
  | Trivial

def Not (p: Prop): Prop := p -> Void

-- Both propositions hold.
type And (p: Prop) (q: Prop): Prop =
  | Both (left: p) (right: q)

-- At least one of the propositions holds: `p || q`.
type Or (p: Prop) (q: Prop): Prop =
  | Inl (left: p)
  | Inr (right: q)

theorem And.left: [p q: Prop] -> And p q -> p
  | Both a b => a

theorem And.right: [p q: Prop] -> And p q -> q
  | Both a b => b

theorem Or.neither: [p q: Prop] -> Not p -> Not q -> Not (Or p q)
  | r, s, Inl a => r a
  | r, s, Inr b => s b

-- From a proof of `Void`, anything follows. `()` means "there's no value to
-- match here", so no right-hand side is needed.
def Void.absurd: Void -> a
  | ()

-- The same for proofs. (Without universe polymorphism, `Void.absurd`'s `a` can
-- only be a type of data.)
def Void.exfalso: [p: Prop] -> Void -> p
  | ()
