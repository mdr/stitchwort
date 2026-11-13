--| `Void`, `Unit`, `Not`, `And`, `Or`, `Iff`, `Exists`, and `absurd`/`exfalso`.
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

theorem Iff.refl ∀ (p: Prop): p ↔ p := { forward = x => x, backward = x => x }

theorem Iff.symm ∀ [p q: Prop] (h: p ↔ q): q ↔ p := { forward = h.backward, backward = h.forward }

theorem Iff.trans ∀ [p q r: Prop] (h: p ↔ q) (k: q ↔ r): p ↔ r :=
  { forward = x => k.forward (h.forward x), backward = x => h.backward (k.backward x) }

--| Some value of `a` satisfies `p`: a witness, and a proof that it does.
--| `Exists (n => n * n = 49)` says there is a number whose square is 49.
type Exists (a: Type) (p: a → Prop): Prop =
  | Witness (value: a) (proof: p value)

--| To prove a proposition from `Exists a p`, take the witness apart: the goal
--| must follow for every value and proof of `p` it might be.
theorem Exists.elim ∀ [p: a → Prop] [goal: Prop] (h: Exists a p) (use: ∀ (x: a) => p x → goal): goal :=
  match h with
    | Witness x proof => use x proof

--| If something satisfies `p`, it's not the case that nothing does.
theorem Exists.notNone ∀ [p: a → Prop] (some: Exists a p) (none: ∀ (x: a) => ¬(p x)): Void :=
  Exists.elim some none

--| A witness for `q` wherever there was one for `p`.
theorem Exists.map ∀ [p: a → Prop] [q: a → Prop] (f: ∀ (x: a) => p x → q x) (h: Exists a p): Exists a q :=
  match h with
    | Witness x proof => Witness x (f x proof)

--| When neither proposition holds, `p || q` doesn't.
theorem Or.neither ∀ [p: Prop] [q: Prop] (r: ¬p) (s: ¬q): ¬(p ∨ q) := match
  | Inl a => r a
  | Inr b => s b

--| From a proof of `Void`, anything follows. `()` means "there's no value to
--| match here", so no right-hand side is needed.
def Void.absurd: (v: Void) → a
  | ()

--| From a proof of `Void`, any proposition follows. (Without universe
--| polymorphism, [`Void.absurd`]'s `a` can only be a type of data.)
def Void.exfalso: [p: Prop] → (v: Void) → p
  | ()
