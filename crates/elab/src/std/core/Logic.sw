--| `Void`, `Unit`, `Not`, `And`, `Or`, `Iff`, and `absurd`/`exfalso`.
-- Loaded with the core: every proof the core states is built from these, and
-- `Decidable`, `deriving` and `auto` write them in full
-- (docs/proposals/prelude-slim.md §2.1).

-- Logic

--| The proposition with no proofs: false.
type Void: Prop

--| The proposition with exactly one proof: true.
type Unit: Prop =
  | Trivial

--| `p` is false: a proof of `p` would give a proof of `Void`. `!p` and `¬p` mean `Not p`.
def Not (p: Prop): Prop := p → Void

--| Both propositions hold: `p && q`. [`And.left`] and [`And.right`] are its fields.
type And (p: Prop) (q: Prop): Prop =
  | Both (left: p) (right: q)

--| At least one of the propositions holds: `p || q`.
type Or (p: Prop) (q: Prop): Prop =
  | Inl (left: p)
  | Inr (right: q)

--| Each of `p` and `q` follows from the other: `p ↔ q`. In the core because
--| the readings of `&&`, `||` and `not` (`Equality.sw`) are stated with it.
type Iff (p: Prop) (q: Prop): Prop = {
  forward: p → q,
  backward: q → p
}

--| When neither proposition holds, `p || q` doesn't.
theorem Or.neither: ∀ [p q: Prop] => ¬p → ¬q → ¬(p ∨ q)
  | r, s, Inl a => r a
  | r, s, Inr b => s b

--| From a proof of `Void`, anything follows. `()` means "there's no value to
--| match here", so no right-hand side is needed.
def Void.absurd: (v: Void) → a
  | ()

--| From a proof of `Void`, any proposition follows. (Without universe
--| polymorphism, [`Void.absurd`]'s `a` can only be a type of data.)
def Void.exfalso: [p: Prop] → (v: Void) → p
  | ()
