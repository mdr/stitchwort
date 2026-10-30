-- What `Decidable.toBool` says about the decision, and `DecEq.sound`. These were
-- in the core (docs/proposals/prelude-slim.md stage 3); no compiler path names
-- them.

theorem Bool.decTrueToBool: (c: Bool) → Decidable.toBool (Bool.decTrue c) = c
  | True => rfl
  | False => rfl

-- What `a == b` (a decision turned into a `Bool`) says about `a = b`, both ways.
theorem Decidable.toBoolSound: [p: Prop] → (d: Decidable p) → Decidable.toBool d = True → p
  | Yes h, e => h
  | No r, e => Void.exfalso (Bool.falseNotTrue e)

theorem Decidable.toBoolFalse: [p: Prop] → (d: Decidable p) → Decidable.toBool d = False → Not p
  | Yes h, e, x => Void.exfalso (Bool.trueNotFalse e)
  | No r, e, x => r x

theorem Decidable.toBoolOf: [p: Prop] → (d: Decidable p) → p → Decidable.toBool d = True
  | Yes h, x => rfl
  | No r, x => Void.exfalso (r x)

theorem Decidable.toBoolOfNot: [p: Prop] → (d: Decidable p) → Not p → Decidable.toBool d = False
  | Yes h, n => Void.exfalso (n h)
  | No r, n => rfl

-- `x == y` says `x = y`.
theorem DecEq.sound [auto decEq: DecEq a] (x: a) (y: a) (h: (x == y) = True): x = y :=
  Decidable.toBoolSound (DecEq.decide x y) h

-- `x == y` is false only for different values.
theorem DecEq.soundFalse [auto eq: DecEq a] (x: a) (y: a) (h: (x == y) = False) (same: x = y): Void :=
  Bool.falseNotTrue (Eq.trans (Eq.sym h) (Decidable.toBoolOf (DecEq.decide x y) same))

-- `x == x`.
theorem DecEq.refl [auto eq: DecEq a] (x: a): (x == x) = True := Decidable.toBoolOf (DecEq.decide x x) rfl

-- `x == y` is `y == x`.
theorem DecEq.eqComm [auto eq: DecEq a] (x: a) (y: a): (x == y) = (y == x) :=
  Bool.eqOf (x == y) (y == x) (h => rewrite DecEq.sound x y h in DecEq.refl y) (h => rewrite DecEq.sound y x h in DecEq.refl x)

-- A closed decidable statement, proved by deciding it: `auto` finds its
-- decision procedure, the elaborator runs it, and the proof is
-- `Decidable.fromYes d Trivial`, which the kernel checks by running `d`
-- again (docs/proposals/decide.md §2, §6.2): `theorem small: 2 + 2 < 5 :=
-- byDecision`, `theorem found: Enter ∈ keys := byDecision`. A false one is
-- `E-AUTO-FALSE`; one whose procedure is stuck on a variable is
-- `E-AUTO-STUCK` (split the variable with `cases`, or check every value
-- with `Finite.check`).
def byDecision [p: Prop] [auto h: p]: p := h
