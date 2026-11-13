--| `Bool` lemmas: `||` and `&&` from their sides and back, implication as
--| `not a || b`, and `Not (x = True)` as `x = False`.
-- They were the opening section of std/List/Sort.sw; they are a file of their
-- own so that a proof that takes a `&&` apart (`omega`'s bridge lemmas,
-- docs/proposals/omega.md §6.4) needn't load the sorting proofs.

--| `||` on `Bool`s: `False` is its unit, `True` absorbs, and it groups and
--| commutes.
theorem Bool.orFalse (b: Bool): (b ∨ False) = b := match b with
  | True => rfl
  | False => rfl

theorem Bool.orTrue (b: Bool): (b ∨ True) = True := match b with
  | True => rfl
  | False => rfl

theorem Bool.orAssoc (a b c: Bool): ((a ∨ b) ∨ c) = (a ∨ (b ∨ c)) := match a with
  | True => rfl
  | False => rfl

theorem Bool.orComm (a b: Bool): (a ∨ b) = (b ∨ a) := match a, b with
  | True, True => rfl
  | True, False => rfl
  | False, True => rfl
  | False, False => rfl

--| `&&` on `Bool`s groups and commutes, as `||` does.
theorem Bool.andAssoc (a b c: Bool): ((a ∧ b) ∧ c) = (a ∧ (b ∧ c)) := match a with
  | True => rfl
  | False => rfl

theorem Bool.andComm (a b: Bool): (a ∧ b) = (b ∧ a) := match a, b with
  | True, True => rfl
  | True, False => rfl
  | False, True => rfl
  | False, False => rfl

--| `&&` from its sides and back; `not a || b` as "a implies b"; two booleans
--| are equal when each implies the other.
theorem Bool.andIntro [a: Bool] [b: Bool] (ha: a = True) (hb: b = True): (a ∧ b) = True := match e: a with
  | True => hb

theorem Bool.andLeft [a: Bool] [b: Bool] (h: (a ∧ b) = True): a = True := match e: a with
  | True => rfl

theorem Bool.andRight [a: Bool] [b: Bool] (h: (a ∧ b) = True): b = True := match e: a with
  | True => h

theorem Bool.impIntro (a b: Bool) (h: a = True → b = True): (¬a ∨ b) = True := match a with
  | True => h rfl
  | False => rfl

theorem Bool.impElim (a b: Bool) (h: (¬a ∨ b) = True) (ha: a = True): b = True := match a with
  | True => h

theorem Bool.eqOf (a b: Bool) (f: a = True → b = True) (g: b = True → a = True): a = b := match a, b with
  | True, True => rfl
  | True, False => cases
  | False, True => cases
  | False, False => rfl

--| A `Bool` that isn't `True` is `False`: `Not (a <= b)` is `Not (Nat.leq a b = True)`,
--| and [`Nat.leqFalse`] takes it from there.
theorem Bool.falseOfNotTrue (x: Bool) (h: x ≠ True): x = False := match x with
  | True => Void.exfalso (h rfl)
  | False => rfl

theorem Bool.falseOfNotTrueExample: Nat.leq 3 2 = False := Bool.falseOfNotTrue (Nat.leq 3 2) Bool.falseNotTrue

theorem Bool.orElim [a: Bool] [b: Bool] [goal: Prop] (h: (a ∨ b) = True) (left: a = True → goal) (right: b = True → goal): goal :=
  match e: a with
    | True => left rfl
    | False => right h

theorem Bool.orLeft [a: Bool] [b: Bool] (h: a = True): (a ∨ b) = True := rewrite h in rfl

theorem Bool.orRight [a: Bool] [b: Bool] (h: b = True): (a ∨ b) = True := match e: a with
  | True => rfl
  | False => h

--| To use `p || q` as a proposition, prove `goal` from each side.
theorem Or.elim [p q: Prop] [goal: Prop] (h: p ∨ q) (left: p → goal) (right: q → goal): goal := match h with
  | Inl x => left x
  | Inr y => right y

--| `||` is `False` exactly when both sides are.
theorem Bool.orFalseLeft (a b: Bool) (h: (a ∨ b) = False): a = False := match a with
  | False => rfl

theorem Bool.orFalseRight (a b: Bool) (h: (a ∨ b) = False): b = False := match a with
  | False => h

theorem Bool.orFalseIntro (a b: Bool) (ha: a = False) (hb: b = False): (a ∨ b) = False := match a with
  | False => hb

--| `&&` is `False` exactly when one side is.
theorem Bool.andFalseElim (a b: Bool) (h: (a ∧ b) = False): (a = False) ∨ (b = False) := match a with
  | True => Inr h
  | False => Inl rfl

theorem Bool.andFalseLeft (a b: Bool) (h: a = False): (a ∧ b) = False := match a with
  | False => rfl

theorem Bool.andFalseRight (a b: Bool) (h: b = False): (a ∧ b) = False := match a with
  | True => h
  | False => rfl

--| `not a` is `True` exactly when `a` is `False`, and the other way round.
theorem Bool.notTrue (a: Bool) (h: (¬a) = True): a = False := match a with
  | False => rfl

theorem Bool.notFalse (a: Bool) (h: (¬a) = False): a = True := match a with
  | True => rfl

theorem Bool.notOfFalse (a: Bool) (h: a = False): (¬a) = True := match a with
  | False => rfl

theorem Bool.notOfTrue (a: Bool) (h: a = True): (¬a) = False := match a with
  | True => rfl

--| `Bool.toNat` is 0 or 1, for `omega` (`omega [Bool.toNatLeOne b]`).
theorem Bool.toNatLeOne (b: Bool): Bool.toNat b ≤ 1 := match b with
  | True => rfl
  | False => rfl
