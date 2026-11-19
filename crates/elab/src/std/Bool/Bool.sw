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

--| `&&` chained is `False` when its last operand is.
theorem Bool.andAndFalse ∀ (a b c: Bool) (no: c = False): (a && b && c) = False := match a, b with
  | True, True => no
  | True, False => byComputing
  | False, _ => byComputing

--| Both sides of a `&&` that is `True` are `True`, as one conjunction.
theorem Bool.andElim ∀ (a b: Bool) (both: (a && b) = True): a = True ∧ b = True :=
  (Bool.andLeft both, Bool.andRight both)

--| A `||` that is `False` is `False` on both sides, as one conjunction.
theorem Bool.orFalseElim ∀ (a b: Bool) (h: (a || b) = False): a = False ∧ b = False := cases

--| `&&` commutes past its left operand: `a && (b && c) = b && (a && c)`.
theorem Bool.andLeftComm ∀ (a b c: Bool): (a && (b && c)) = (b && (a && c)) := cases

--| `(a && b) && c = b && (a && c)`: the left grouping reassociated with the first two swapped.
theorem Bool.andShuffle ∀ (a b c: Bool): ((a && b) && c) = (b && (a && c)) := cases

--| A `||` that is `True` stays `True` with its sides swapped.
theorem Bool.orSwapTrue ∀ (x y: Bool) (or: (x || y) = True): (y || x) = True := match x with
  | True => rewrite Bool.orTrue y
  | False => rewrite or

--| A `||` that is `True` with a `False` left side has a `True` right side.
theorem Bool.orOfLeftFalse ∀ (a b: Bool) (h: (a || b) = True) (off: a = False): b = True := cases

--| A `||` that is `True` with a `False` right side has a `True` left side.
theorem Bool.orOfRightFalse ∀ (x s: Bool) (h: (x || s) = True) (off: s = False): x = True := cases

--| `b || False` is `True` only when `b` is.
theorem Bool.orFalseTrue ∀ (b: Bool) (h: (b || False) = True): b = True := match b with | True => byComputing

--| Two `Bool`s that compare `==` are equal.
theorem Bool.eqOfBeq ∀ (a b: Bool) (h: (a == b) = True): a = b := cases

--| A `||` that is `True` stays `True` with a further operand on the right.
theorem Bool.orExtend ∀ (a b c: Bool) (h: (a || b) = True): (a || b || c) = True := cases

--| `x || (a && b)` being `True` makes `x || a` `True`.
theorem Bool.orAndLeft ∀ (x a b: Bool) (h: (x || (a && b)) = True): (x || a) = True := cases

--| `a || !b` being `True` with `b` `True` makes `a` `True`.
theorem Bool.orOfNotTrue ∀ (a b: Bool) (h: (a || !b) = True) (on: b = True): a = True := cases

--| `!x || False` being `True` makes `x` `False`.
theorem Bool.notOrFalse ∀ (x: Bool) (h: (!x || False) = True): x = False := cases

--| A chained `&&` is `False` when its first two operands already make `False`.
theorem Bool.andFalseLeftOf ∀ (a b c: Bool) (no: (a && b) = False): (a && b && c) = False := match a, b, no with
  | True, True, no => (Bool.falseNotTrue no.flipped).impossible
  | True, False, no => byComputing
  | False, _, no => byComputing

--| A chained `&&` is `False` when its middle operand is.
theorem Bool.andFalseMiddle ∀ (a c: Bool): (a && False && c) = False := match a with
  | True => byComputing
  | False => byComputing
