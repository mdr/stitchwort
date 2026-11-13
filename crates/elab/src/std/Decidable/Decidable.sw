--| What `Decidable.holds` says about the decision, and [`DecEq.sound`].
-- These were in the core (docs/proposals/prelude-slim.md stage 3).

--| Double negation of a decided proposition: what `¬(n ≠ 3)` says about `n = 3`.
theorem Decidable.notNotOf ∀ [p: Prop] (d: Decidable p) (n: ¬¬p): p := match e: d.holds with
  | True => d.sound e
  | False => Void.exfalso (n (Decidable.refute d e))

--| `x == y` says `x = y`.
theorem DecEq.sound ∀ [auto decEq: DecEq a] [x: a] [y: a] (h: (x == y) = True): x = y :=
  (DecEq.decide x y).sound h

--| `x == y` is false only for different values.
theorem DecEq.soundFalse ∀ [auto eq: DecEq a] (x: a) (y: a) (h: (x == y) = False) (same: x = y): Void :=
  Bool.falseNotTrue (Eq.trans (Eq.sym h) ((DecEq.decide x y).complete same))

--| `x == x` is `True`, for any `DecEq` instance.
theorem DecEq.refl ∀ [auto eq: DecEq a] (x: a): (x == x) = True := (DecEq.decide x x).complete rfl

--| `x != y` false says `x = y`.
theorem DecEq.neFalse ∀ [auto eq: DecEq a] (x: a) (y: a) (h: ((x != y): Bool) = False): x = y :=
  Decidable.notNotOf (DecEq.decide x y) (differ => Bool.falseNotTrue (Eq.trans (Eq.sym h) ((Decidable.not (DecEq.decide x y)).complete differ)))

--| `x != y` true says they differ; the converse of [`DecEq.trueOfNe`].
theorem DecEq.neTrue ∀ [auto eq: DecEq a] [x: a] [y: a] (h: ((x != y): Bool) = True): x ≠ y :=
  same => Bool.falseNotTrue (rewrite Decidable.toBoolOfNot (Decidable.not (DecEq.decide x y)) (differ => differ same) at h)

--| `x ≠ y` says `x != y`; the converse of [`DecEq.neTrue`].
theorem DecEq.trueOfNe ∀ [auto eq: DecEq a] [x: a] [y: a] (h: x ≠ y): ((x != y): Bool) = True :=
  (Decidable.not (DecEq.decide x y)).complete h

--| `x ≠ y` says `x == y` is false; the converse of [`DecEq.soundFalse`].
theorem DecEq.falseOfNe ∀ [auto eq: DecEq a] [x: a] [y: a] (h: x ≠ y): (x == y) = False :=
  Decidable.toBoolOfNot (DecEq.decide x y) h

--| A nonzero factor on the right doesn't change `==`: cancelling, as a `Bool`.
-- It is here, not beside [`Nat.mulRightCancel`] in std/Nat/Arith.sw, because
-- it uses [`DecEq.refl`]: in Arith.sw it made every program that loads the
-- list toolkit load this file too.
theorem Nat.mulRightCancelBool ∀ [a: Nat] [b: Nat] [c: Nat] (nz: c ≠ 0): (a * c == b * c) = (a == b) :=
  if same: a = b then rewrite same, DecEq.refl (b * c), DecEq.refl b in rfl
  else rewrite DecEq.falseOfNe same, DecEq.falseOfNe (e => same (Nat.mulRightCancel a b c nz e)) in rfl

--| A value is never `!=` to itself.
theorem DecEq.neSelf ∀ [auto eq: DecEq a] (x: a): ((x != x): Bool) = False := match e: ((x != x): Bool) with
  | True => Void.exfalso (DecEq.neTrue e rfl)
  | False => rfl

--| `x == y` is `y == x`.
theorem DecEq.eqComm ∀ [auto eq: DecEq a] (x: a) (y: a): (x == y) = (y == x) :=
  Bool.eqOf (x == y) (y == x) (h => rewrite DecEq.sound h in DecEq.refl y) (h => rewrite DecEq.sound h in DecEq.refl x)

--| A closed decidable statement, proved by deciding it.
--| `auto` finds its decision procedure, the elaborator runs it, and the proof
--| is `d.sound rfl`, which the kernel checks by running `d`'s test
--| again: `theorem small: 2 + 2 < 5 := byDecision`, `theorem found: Enter ∈
--| keys := byDecision`. A false one is `E-AUTO-FALSE`; one whose procedure is
--| stuck on a variable is `E-AUTO-STUCK` (split the variable with `cases`, or
--| check every value with [`Finite.check`]).
-- (docs/proposals/decide.md §2, §6.2)
def byDecision [p: Prop] [auto h: p]: p := h
