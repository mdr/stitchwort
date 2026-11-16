--| `Bool` lemmas: `||` and `&&` from their sides and back, implication as
--| `not a || b`, and `Not (x = True)` as `x = False`.
-- They were the opening section of std/List/Sort.sw; they are a file of their
-- own so that a proof that takes a `&&` apart (`arithmetic`'s bridge lemmas,
-- docs/proposals/omega.md §6.4) needn't load the sorting proofs.

--| `||` on `Bool`s: `False` is its unit, `True` absorbs, and it groups and
--| commutes.
theorem Bool.orFalse ∀ (b: Bool): (b ∨ False) = b := match b with
  | True => byComputing
  | False => byComputing

theorem Bool.orTrue ∀ (b: Bool): (b ∨ True) = True := match b with
  | True => byComputing
  | False => byComputing

theorem Bool.orAssoc ∀ (a b c: Bool): ((a ∨ b) ∨ c) = (a ∨ (b ∨ c)) := match a with
  | True => byComputing
  | False => byComputing

theorem Bool.orComm ∀ (a b: Bool): (a ∨ b) = (b ∨ a) := match a, b with
  | True, True => byComputing
  | True, False => byComputing
  | False, True => byComputing
  | False, False => byComputing

--| `&&` on `Bool`s groups and commutes, as `||` does.
theorem Bool.andAssoc ∀ (a b c: Bool): ((a ∧ b) ∧ c) = (a ∧ (b ∧ c)) := match a with
  | True => byComputing
  | False => byComputing

theorem Bool.andComm ∀ (a b: Bool): (a ∧ b) = (b ∧ a) := match a, b with
  | True, True => byComputing
  | True, False => byComputing
  | False, True => byComputing
  | False, False => byComputing

--| `&&` from its sides and back; `not a || b` as "a implies b"; two booleans
--| are equal when each implies the other.
theorem Bool.andIntro ∀ [a b: Bool] (ha: a = True) (hb: b = True): (a ∧ b) = True := match e: a with | True => hb

theorem Bool.andLeft ∀ [a b: Bool] (h: (a ∧ b) = True): a = True := match e: a with | True => byComputing

theorem Bool.andRight ∀ [a b: Bool] (h: (a ∧ b) = True): b = True := match e: a with | True => h

theorem Bool.impIntro ∀ (a b: Bool) (h: a = True → b = True): (¬a ∨ b) = True := match a with
  | True => h byComputing
  | False => byComputing

theorem Bool.impElim ∀ (a b: Bool) (h: (¬a ∨ b) = True) (ha: a = True): b = True := match a with | True => h

theorem Bool.eqOf ∀ (a b: Bool) (f: a = True → b = True) (g: b = True → a = True): a = b := match a, b with
  | True, True => byComputing
  | True, False => cases
  | False, True => cases
  | False, False => byComputing

--| A `Bool` that isn't `True` is `False`: `Not (a <= b)` is `Not (Nat.leq a b = True)`,
--| and [`Nat.leqFalse`] takes it from there.
theorem Bool.falseOfNotTrue ∀ (x: Bool) (h: x ≠ True): x = False := match x with
  | True => (h byComputing).impossible
  | False => byComputing

theorem Bool.falseOfNotTrueExample: Nat.leq 3 2 = False := Bool.falseOfNotTrue (Nat.leq 3 2) Bool.falseNotTrue

theorem Bool.orElim ∀ [a b: Bool] [goal: Prop]
    (h: (a ∨ b) = True)
    (left: a = True → goal) (right: b = True → goal):
    goal :=
  match e: a with
    | True => left byComputing
    | False => right h

theorem Bool.orLeft ∀ [a b: Bool] (h: a = True): (a ∨ b) = True := rewrite h

theorem Bool.orRight ∀ [a b: Bool] (h: b = True): (a ∨ b) = True := match e: a with
  | True => byComputing
  | False => h

--| To use `p || q` as a proposition, prove `goal` from each side.
theorem Or.elim ∀ [p q goal: Prop] (h: p ∨ q) (left: p → goal) (right: q → goal): goal := match h with
  | Inl x => left x
  | Inr y => right y

--| `||` is `False` exactly when both sides are.
theorem Bool.orFalseLeft ∀ (a b: Bool) (h: (a ∨ b) = False): a = False := match a with | False => byComputing

theorem Bool.orFalseRight ∀ (a b: Bool) (h: (a ∨ b) = False): b = False := match a with | False => h

theorem Bool.orFalseIntro ∀ (a b: Bool) (ha: a = False) (hb: b = False): (a ∨ b) = False := match a with | False => hb

--| `&&` is `False` exactly when one side is.
theorem Bool.andFalseElim ∀ (a b: Bool) (h: (a ∧ b) = False): (a = False) ∨ (b = False) := match a with
  | True => Inr h
  | False => Inl byComputing

theorem Bool.andFalseLeft ∀ (a b: Bool) (h: a = False): (a ∧ b) = False := match a with | False => byComputing

theorem Bool.andFalseRight ∀ (a b: Bool) (h: b = False): (a ∧ b) = False := match a with
  | True => h
  | False => byComputing

--| `not a` is `True` exactly when `a` is `False`, and the other way round.
theorem Bool.notTrue ∀ (a: Bool) (h: (¬a) = True): a = False := match a with | False => byComputing

theorem Bool.notFalse ∀ (a: Bool) (h: (¬a) = False): a = True := match a with | True => byComputing

theorem Bool.notOfFalse ∀ (a: Bool) (h: a = False): (¬a) = True := match a with | False => byComputing

theorem Bool.notOfTrue ∀ (a: Bool) (h: a = True): (¬a) = False := match a with | True => byComputing

--| `Bool.toNat` is 0 or 1, for `arithmetic` (`arithmetic [Bool.toNatLeOne b]`).
theorem Bool.toNatLeOne ∀ (b: Bool): Bool.toNat b ≤ 1 := match b with
  | True => byComputing
  | False => byComputing
