--| What `Decidable.holds` says about the decision, and [`DecEq.sound`].
-- These were in the core (docs/proposals/prelude-slim.md stage 3). `omega`'s
-- proofs and guarded arms' generated equations name the `toBool` ones.

theorem Bool.decTrueToBool (c: Bool): Decidable.holds (Bool.decTrue c) = c := rfl

--| What `a == b` (a decision turned into a `Bool`) says about `a = b`, both ways.
theorem Decidable.toBoolSound [p: Prop] (d: Decidable p) (e: Decidable.holds d = True): p := d.sound e

theorem Decidable.toBoolFalse: ∀ [p: Prop] (d: Decidable p) => Decidable.holds d = False → ¬p
  | d, e, x => Decidable.refute d e x

theorem Decidable.toBoolOf [p: Prop] (d: Decidable p) (x: p): Decidable.holds d = True := d.complete x

theorem Decidable.toBoolOfNot [p: Prop] (d: Decidable p) (n: ¬p): Decidable.holds d = False :=
  match d with
    | { holds = True, sound = s, complete = c } => Void.exfalso (n (s rfl))
    | { holds = False, sound = s, complete = c } => rfl

--| Double negation of a decided proposition: what `¬(n ≠ 3)` says about `n = 3`.
theorem Decidable.notNotOf [p: Prop] (d: Decidable p) (n: ¬¬p): p :=
  match e: d.holds with
    | True => d.sound e
    | False => Void.exfalso (n (Decidable.refute d e))

--| What `a && b` says about `p ∧ q`, where `a` and `b` are the decisions' `Bool`s
--| (`toBool dp = a`): the same four facts as `toBoolOf` and the others, for a
--| guard `p && q` stated as the conjunction.
theorem Decidable.andBoolOf [p q: Prop] (dp: Decidable p) (dq: Decidable q) (a b: Bool) (ea: Decidable.holds dp = a) (eb: Decidable.holds dq = b) (h: p ∧ q): (a && b) = True :=
  match a, b with
    | True, True => rfl
    | True, False => Void.exfalso (Bool.falseNotTrue (Eq.trans (Eq.sym eb) (Decidable.toBoolOf dq (And.right h))))
    | False, b => Void.exfalso (Bool.falseNotTrue (Eq.trans (Eq.sym ea) (Decidable.toBoolOf dp (And.left h))))

theorem Decidable.andBoolOfNot [p q: Prop] (dp: Decidable p) (dq: Decidable q) (a b: Bool) (ea: Decidable.holds dp = a) (eb: Decidable.holds dq = b) (n: ¬(p ∧ q)): (a && b) = False :=
  match a, b with
    | True, True => Void.exfalso (n (Both (Decidable.toBoolSound dp ea) (Decidable.toBoolSound dq eb)))
    | True, False => rfl
    | False, b => rfl

theorem Decidable.andBoolSound [p q: Prop] (dp: Decidable p) (dq: Decidable q) (a b: Bool) (ea: Decidable.holds dp = a) (eb: Decidable.holds dq = b) (h: (a && b) = True): p ∧ q :=
  match a, b with
    | True, True => Both (Decidable.toBoolSound dp ea) (Decidable.toBoolSound dq eb)
    | True, False => cases
    | False, b => cases

theorem Decidable.andBoolFalse: ∀ [p q: Prop] (dp: Decidable p) (dq: Decidable q) (a b: Bool) => Decidable.holds dp = a → Decidable.holds dq = b → (a && b) = False → ¬(p ∧ q)
  | dp, dq, True, True, ea, eb, h, n => cases
  | dp, dq, True, False, ea, eb, h, n => Decidable.toBoolFalse dq eb (And.right n)
  | dp, dq, False, b, ea, eb, h, n => Decidable.toBoolFalse dp ea (And.left n)

--| A conjunction `p && q` decided by [`Decidable.and`] has the `Bool` `a && b`
--| of its sides' (`toBool dp = a`): what lets a guard `p && q && r` be stated
--| as `p ∧ q ∧ r`.
theorem Decidable.andBoolDec [p q: Prop] (dp: Decidable p) (dq: Decidable q) (a b: Bool) (ea: Decidable.holds dp = a) (eb: Decidable.holds dq = b): Decidable.holds (Decidable.and dp dq) = (a && b) :=
  J (a' e => Decidable.holds (Decidable.and dp dq) = (a' && b)) (J (b' e => Decidable.holds (Decidable.and dp dq) = (dp.holds && b')) rfl eb) ea

--| `x == y` says `x = y`.
theorem DecEq.sound [auto decEq: DecEq a] [x: a] [y: a] (h: (x == y) = True): x = y :=
  Decidable.toBoolSound (DecEq.decide x y) h

--| `x == y` is false only for different values.
theorem DecEq.soundFalse [auto eq: DecEq a] (x: a) (y: a) (h: (x == y) = False) (same: x = y): Void :=
  Bool.falseNotTrue (Eq.trans (Eq.sym h) (Decidable.toBoolOf (DecEq.decide x y) same))

--| `x == x` is `True`, for any `DecEq` instance.
theorem DecEq.refl [auto eq: DecEq a] (x: a): (x == x) = True := Decidable.toBoolOf (DecEq.decide x x) rfl

--| `x != y` false says `x = y`.
theorem DecEq.neFalse [auto eq: DecEq a] (x: a) (y: a) (h: ((x != y): Bool) = False): x = y :=
  Decidable.notNotOf (DecEq.decide x y) (differ => Bool.falseNotTrue (Eq.trans (Eq.sym h) (Decidable.toBoolOf (Decidable.not (DecEq.decide x y)) differ)))

--| `x != y` true says they differ; the converse of [`DecEq.trueOfNe`].
theorem DecEq.neTrue [auto eq: DecEq a] [x: a] [y: a] (h: ((x != y): Bool) = True): x ≠ y :=
  same => Bool.falseNotTrue (rewrite Decidable.toBoolOfNot (Decidable.not (DecEq.decide x y)) (differ => differ same) at h)

--| `x ≠ y` says `x != y`; the converse of [`DecEq.neTrue`].
theorem DecEq.trueOfNe [auto eq: DecEq a] [x: a] [y: a] (h: x ≠ y): ((x != y): Bool) = True :=
  Decidable.toBoolOf (Decidable.not (DecEq.decide x y)) h

--| `x ≠ y` says `x == y` is false; the converse of [`DecEq.soundFalse`].
theorem DecEq.falseOfNe [auto eq: DecEq a] [x: a] [y: a] (h: x ≠ y): (x == y) = False :=
  Decidable.toBoolOfNot (DecEq.decide x y) h

--| A nonzero factor on the right doesn't change `==`: cancelling, as a `Bool`.
-- It is here, not beside [`Nat.mulRightCancel`] in std/Nat/Arith.sw, because
-- it uses [`DecEq.refl`]: in Arith.sw it made every program that loads the
-- list toolkit load this file too.
theorem Nat.mulRightCancelBool [a: Nat] [b: Nat] [c: Nat] (nz: c ≠ 0): (a * c == b * c) = (a == b) :=
  if same: a = b then rewrite same, DecEq.refl (b * c), DecEq.refl b in rfl
  else rewrite DecEq.falseOfNe same, DecEq.falseOfNe (e => same (Nat.mulRightCancel a b c nz e)) in rfl

--| A value is never `!=` to itself.
theorem DecEq.neSelf [auto eq: DecEq a] (x: a): ((x != x): Bool) = False :=
  match e: ((x != x): Bool) with
    | True => Void.exfalso (DecEq.neTrue e rfl)
    | False => rfl

--| `x == y` is `y == x`.
theorem DecEq.eqComm [auto eq: DecEq a] (x: a) (y: a): (x == y) = (y == x) :=
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
