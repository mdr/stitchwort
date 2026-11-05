--| What `Decidable.toBool` says about the decision, and [`DecEq.sound`].
-- These were in the core (docs/proposals/prelude-slim.md stage 3). `omega`'s
-- proofs and guarded arms' generated equations name the `toBool` ones.

theorem Bool.decTrueToBool: (c: Bool) → Decidable.toBool (Bool.decTrue c) = c
  | True => rfl
  | False => rfl

--| What `a == b` (a decision turned into a `Bool`) says about `a = b`, both ways.
theorem Decidable.toBoolSound: [p: Prop] → (d: Decidable p) → Decidable.toBool d = True → p
  | Yes h, e => h
  | No r, e => Void.exfalso (Bool.falseNotTrue e)

theorem Decidable.toBoolFalse: [p: Prop] → (d: Decidable p) → Decidable.toBool d = False → ¬p
  | Yes h, e, x => Void.exfalso (Bool.trueNotFalse e)
  | No r, e, x => r x

theorem Decidable.toBoolOf: [p: Prop] → (d: Decidable p) → p → Decidable.toBool d = True
  | Yes h, x => rfl
  | No r, x => Void.exfalso (r x)

theorem Decidable.toBoolOfNot: [p: Prop] → (d: Decidable p) → ¬p → Decidable.toBool d = False
  | Yes h, n => Void.exfalso (n h)
  | No r, n => rfl

--| `x == y` says `x = y`.
theorem DecEq.sound [auto decEq: DecEq a] (x: a) (y: a) (h: (x == y) = True): x = y :=
  Decidable.toBoolSound (DecEq.decide x y) h

--| `x == y` is false only for different values.
theorem DecEq.soundFalse [auto eq: DecEq a] (x: a) (y: a) (h: (x == y) = False) (same: x = y): Void :=
  Bool.falseNotTrue (Eq.trans (Eq.sym h) (Decidable.toBoolOf (DecEq.decide x y) same))

--| `x == x` is `True`, for any `DecEq` instance.
theorem DecEq.refl [auto eq: DecEq a] (x: a): (x == x) = True := Decidable.toBoolOf (DecEq.decide x x) rfl

--| `x != y` false says `x = y`; true says they differ.
theorem DecEq.neFalse [auto eq: DecEq a] (x: a) (y: a) (h: ((x != y): Bool) = False): x = y :=
  match d: DecEq.decide x y with
    | Yes same => same
    | No differ => Void.exfalso (Bool.trueNotFalse h)

theorem DecEq.neTrue [auto eq: DecEq a] (x: a) (y: a) (h: ((x != y): Bool) = True): x ≠ y :=
  same => Bool.falseNotTrue (rewrite Decidable.toBoolOfNot (Decidable.not (DecEq.decide x y)) (differ => differ same) at h)

--| A nonzero factor on the right doesn't change `==`: cancelling, as a `Bool`.
-- It is here, not beside [`Nat.mulRightCancel`] in std/Nat/Arith.sw, because
-- it uses [`DecEq.refl`]: in Arith.sw it made every program that loads the
-- list toolkit load this file too.
theorem Nat.mulRightCancelBool (a: Nat) (b: Nat) (c: Nat) (nz: c ≠ 0): (a * c == b * c) = (a == b) :=
  match Nat.decEq a b with
    | Yes same => rewrite same, DecEq.refl (b * c) in rfl
    | No differ =>
      match Nat.decEq (a * c) (b * c) with
        | Yes e => Void.exfalso (differ (Nat.mulRightCancel a b c nz e))
        | No e => rfl

--| `x == y` is `y == x`.
theorem DecEq.eqComm [auto eq: DecEq a] (x: a) (y: a): (x == y) = (y == x) :=
  Bool.eqOf (x == y) (y == x) (h => rewrite DecEq.sound x y h in DecEq.refl y) (h => rewrite DecEq.sound y x h in DecEq.refl x)

--| A closed decidable statement, proved by deciding it.
--| `auto` finds its decision procedure, the elaborator runs it, and the proof
--| is `Decidable.fromYes d Trivial`, which the kernel checks by running `d`
--| again: `theorem small: 2 + 2 < 5 := byDecision`, `theorem found: Enter ∈
--| keys := byDecision`. A false one is `E-AUTO-FALSE`; one whose procedure is
--| stuck on a variable is `E-AUTO-STUCK` (split the variable with `cases`, or
--| check every value with [`Finite.check`]).
-- (docs/proposals/decide.md §2, §6.2)
def byDecision [p: Prop] [auto h: p]: p := h
