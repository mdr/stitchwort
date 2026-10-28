-- `Bool` lemmas: `||` and `&&` from their sides and back, implication as
-- `not a || b`, and `Not (x = True)` as `x = False`. They were the opening
-- section of std/List/Sort.sw; they are a file of their own so that a proof
-- that takes a `&&` apart (`omega`'s bridge lemmas, docs/proposals/omega.md
-- §6.4) needn't load the sorting proofs.

-- `||` on `Bool`s: `False` is its unit, `True` absorbs, and it groups and
-- commutes.
theorem Bool.orFalse: (b: Bool) → (b ∨ False) = b
  | True => rfl
  | False => rfl

theorem Bool.orTrue: (b: Bool) → (b ∨ True) = True
  | True => rfl
  | False => rfl

theorem Bool.orAssoc: (a: Bool) → (b: Bool) → (c: Bool) → ((a ∨ b) ∨ c) = (a ∨ (b ∨ c))
  | True, b, c => rfl
  | False, b, c => rfl

theorem Bool.orComm: (a: Bool) → (b: Bool) → (a ∨ b) = (b ∨ a)
  | True, True => rfl
  | True, False => rfl
  | False, True => rfl
  | False, False => rfl

-- `&&` from its sides and back; `not a || b` as "a implies b"; two booleans
-- are equal when each implies the other.
theorem Bool.andIntro: (a: Bool) → (b: Bool) → a = True → b = True → (a ∧ b) = True
  | True, b, ha, hb => hb
  | False, b, ha, hb => Void.exfalso (Bool.falseNotTrue ha)

theorem Bool.andLeft: (a: Bool) → (b: Bool) → (a ∧ b) = True → a = True
  | True, b, h => rfl
  | False, b, h => Void.exfalso (Bool.falseNotTrue h)

theorem Bool.andRight: (a: Bool) → (b: Bool) → (a ∧ b) = True → b = True
  | True, b, h => h
  | False, b, h => Void.exfalso (Bool.falseNotTrue h)

theorem Bool.impIntro: (a: Bool) → (b: Bool) → (a = True → b = True) → (¬a ∨ b) = True
  | True, b, h => h rfl
  | False, b, h => rfl

theorem Bool.impElim: (a: Bool) → (b: Bool) → (¬a ∨ b) = True → a = True → b = True
  | True, b, h, ha => h
  | False, b, h, ha => Void.exfalso (Bool.falseNotTrue ha)

theorem Bool.eqOf: (a: Bool) → (b: Bool) → (a = True → b = True) → (b = True → a = True) → a = b
  | True, True, f, g => rfl
  | True, False, f, g => Void.exfalso (Bool.falseNotTrue (f rfl))
  | False, True, f, g => Void.exfalso (Bool.falseNotTrue (g rfl))
  | False, False, f, g => rfl

-- A `Bool` that isn't `True` is `False`: `Not (a <= b)` is `Not (Nat.leq a b = True)`,
-- and `Nat.leqFalse` takes it from there.
theorem Bool.falseOfNotTrue: (x: Bool) → Not (x = True) → x = False
  | True, h => Void.exfalso (h rfl)
  | False, h => rfl

theorem Bool.falseOfNotTrueExample: Nat.leq 3 2 = False := Bool.falseOfNotTrue (Nat.leq 3 2) Bool.falseNotTrue

theorem Bool.orElim (a: Bool) (b: Bool) (goal: Prop) (h: (a ∨ b) = True) (left: a = True → goal) (right: b = True → goal): goal :=
  match e: a with
    | True => left rfl
    | False => right h

theorem Bool.orLeft (a: Bool) (b: Bool) (h: a = True): (a ∨ b) = True := rewrite h in rfl

theorem Bool.orRight (a: Bool) (b: Bool) (h: b = True): (a ∨ b) = True :=
  match e: a with
    | True => rfl
    | False => h

-- The same for a proposition: prove `goal` from each side.
theorem Or.elim [p q: Prop] [goal: Prop] (h: Or p q) (left: p → goal) (right: q → goal): goal :=
  match h with
    | Inl x => left x
    | Inr y => right y

-- `||` is `False` exactly when both sides are.
theorem Bool.orFalseLeft: (a: Bool) → (b: Bool) → (a ∨ b) = False → a = False
  | True, b, h => Void.exfalso (Bool.trueNotFalse h)
  | False, b, h => rfl

theorem Bool.orFalseRight: (a: Bool) → (b: Bool) → (a ∨ b) = False → b = False
  | True, b, h => Void.exfalso (Bool.trueNotFalse h)
  | False, b, h => h

theorem Bool.orFalseIntro: (a: Bool) → (b: Bool) → a = False → b = False → (a ∨ b) = False
  | True, b, ha, hb => Void.exfalso (Bool.trueNotFalse ha)
  | False, b, ha, hb => hb

-- `&&` is `False` exactly when one side is.
theorem Bool.andFalseElim: (a: Bool) → (b: Bool) → (a ∧ b) = False → Or (a = False) (b = False)
  | True, b, h => Inr h
  | False, b, h => Inl rfl

theorem Bool.andFalseLeft: (a: Bool) → (b: Bool) → a = False → (a ∧ b) = False
  | True, b, h => Void.exfalso (Bool.trueNotFalse h)
  | False, b, h => rfl

theorem Bool.andFalseRight: (a: Bool) → (b: Bool) → b = False → (a ∧ b) = False
  | True, b, h => h
  | False, b, h => rfl

-- `not a` is `True` exactly when `a` is `False`, and the other way round.
theorem Bool.notTrue: (a: Bool) → (¬a) = True → a = False
  | True, h => Void.exfalso (Bool.falseNotTrue h)
  | False, h => rfl

theorem Bool.notFalse: (a: Bool) → (¬a) = False → a = True
  | True, h => rfl
  | False, h => Void.exfalso (Bool.trueNotFalse h)

theorem Bool.notOfFalse: (a: Bool) → a = False → (¬a) = True
  | True, h => Void.exfalso (Bool.trueNotFalse h)
  | False, h => rfl

theorem Bool.notOfTrue: (a: Bool) → a = True → (¬a) = False
  | True, h => rfl
  | False, h => Void.exfalso (Bool.falseNotTrue h)
