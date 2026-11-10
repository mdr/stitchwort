--| What `Decidable.toBool` says about the decision, and [`DecEq.sound`].
-- These were in the core (docs/proposals/prelude-slim.md stage 3). `omega`'s
-- proofs and guarded arms' generated equations name the `toBool` ones.

theorem Bool.decTrueToBool (c: Bool): Decidable.toBool (Bool.decTrue c) = c :=
  match c with
    | True => rfl
    | False => rfl

--| What `a == b` (a decision turned into a `Bool`) says about `a = b`, both ways.
theorem Decidable.toBoolSound [p: Prop] (d: Decidable p) (e: Decidable.toBool d = True): p :=
  match d with
    | Yes h => h
    | No r => cases

theorem Decidable.toBoolFalse: ∀ [p: Prop] (d: Decidable p) => Decidable.toBool d = False → ¬p
  | Yes h, e, x => cases
  | No r, e, x => r x

--| What a decision's `Bool` says when it is `True`: the proof of `p`.
theorem Decidable.sound [p: Prop] (d: Decidable p) (e: Decidable.does d = True): p := Decidable.toBoolSound d e

--| What a decision's `Bool` says when it is `False`: `p` is refuted. Splitting
--| on the test (`match h: x < y with | True => … | False => …`) and then
--| calling [`Decidable.sound`] or this on its equation `h` is how a proof gets
--| the evidence a `match` on the decision would have bound.
theorem Decidable.refute [p: Prop] (d: Decidable p) (e: Decidable.does d = False): ¬p := Decidable.toBoolFalse d e

theorem Decidable.toBoolOf [p: Prop] (d: Decidable p) (x: p): Decidable.toBool d = True :=
  match d with
    | Yes h => rfl
    | No r => Void.exfalso (r x)

theorem Decidable.toBoolOfNot [p: Prop] (d: Decidable p) (n: ¬p): Decidable.toBool d = False :=
  match d with
    | Yes h => Void.exfalso (n h)
    | No r => rfl

--| Double negation of a decided proposition: what `¬(n ≠ 3)` says about `n = 3`.
theorem Decidable.notNotOf [p: Prop] (d: Decidable p) (n: ¬¬p): p :=
  match d with
    | Yes h => h
    | No r => Void.exfalso (n r)

--| What `a && b` says about `p ∧ q`, where `a` and `b` are the decisions' `Bool`s
--| (`toBool dp = a`): the same four facts as `toBoolOf` and the others, for a
--| guard `p && q` stated as the conjunction.
theorem Decidable.andBoolOf [p q: Prop] (dp: Decidable p) (dq: Decidable q) (a b: Bool) (ea: Decidable.toBool dp = a) (eb: Decidable.toBool dq = b) (h: p ∧ q): (a && b) = True :=
  match a, b with
    | True, True => rfl
    | True, False => Void.exfalso (Bool.falseNotTrue (Eq.trans (Eq.sym eb) (Decidable.toBoolOf dq (And.right h))))
    | False, b => Void.exfalso (Bool.falseNotTrue (Eq.trans (Eq.sym ea) (Decidable.toBoolOf dp (And.left h))))

theorem Decidable.andBoolOfNot [p q: Prop] (dp: Decidable p) (dq: Decidable q) (a b: Bool) (ea: Decidable.toBool dp = a) (eb: Decidable.toBool dq = b) (n: ¬(p ∧ q)): (a && b) = False :=
  match a, b with
    | True, True => Void.exfalso (n (Both (Decidable.toBoolSound dp ea) (Decidable.toBoolSound dq eb)))
    | True, False => rfl
    | False, b => rfl

theorem Decidable.andBoolSound [p q: Prop] (dp: Decidable p) (dq: Decidable q) (a b: Bool) (ea: Decidable.toBool dp = a) (eb: Decidable.toBool dq = b) (h: (a && b) = True): p ∧ q :=
  match a, b with
    | True, True => Both (Decidable.toBoolSound dp ea) (Decidable.toBoolSound dq eb)
    | True, False => cases
    | False, b => cases

theorem Decidable.andBoolFalse: ∀ [p q: Prop] (dp: Decidable p) (dq: Decidable q) (a b: Bool) => Decidable.toBool dp = a → Decidable.toBool dq = b → (a && b) = False → ¬(p ∧ q)
  | dp, dq, True, True, ea, eb, h, n => cases
  | dp, dq, True, False, ea, eb, h, n => Decidable.toBoolFalse dq eb (And.right n)
  | dp, dq, False, b, ea, eb, h, n => Decidable.toBoolFalse dp ea (And.left n)

--| A conjunction `p && q` decided by [`Decidable.and`] has the `Bool` `a && b`
--| of its sides' (`toBool dp = a`): what lets a guard `p && q && r` be stated
--| as `p ∧ q ∧ r`.
theorem Decidable.andBoolDec [p q: Prop] (dp: Decidable p) (dq: Decidable q) (a b: Bool) (ea: Decidable.toBool dp = a) (eb: Decidable.toBool dq = b): Decidable.toBool (Decidable.and dp dq) = (a && b) :=
  match dp, dq, a, b with
    | Yes x, Yes y, True, True => rfl
    | Yes x, Yes y, True, False => cases
    | Yes x, Yes y, False, b => cases
    | Yes x, No r, True, True => cases
    | Yes x, No r, True, False => rfl
    | Yes x, No r, False, b => cases
    | No r, dq, True, b => cases
    | No r, dq, False, b => rfl

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
  match d: DecEq.decide x y with
    | Yes same => same
    | No differ => cases

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
  match Nat.decEq a b with
    | Yes same => rewrite same, DecEq.refl (b * c) in rfl
    | No differ =>
      match Nat.decEq (a * c) (b * c) with
        | Yes e => Void.exfalso (differ (Nat.mulRightCancel a b c nz e))
        | No e => rfl

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
--| is `Decidable.fromYes d Trivial`, which the kernel checks by running `d`
--| again: `theorem small: 2 + 2 < 5 := byDecision`, `theorem found: Enter ∈
--| keys := byDecision`. A false one is `E-AUTO-FALSE`; one whose procedure is
--| stuck on a variable is `E-AUTO-STUCK` (split the variable with `cases`, or
--| check every value with [`Finite.check`]).
-- (docs/proposals/decide.md §2, §6.2)
def byDecision [p: Prop] [auto h: p]: p := h
