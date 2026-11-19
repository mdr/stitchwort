--| `Bool` lemmas: `||` and `&&` from their sides and back, implication as
--| `not a || b`, and `Not (x = True)` as `x = False`.
-- They were the opening section of std/List/Sort.sw; they are a file of their
-- own so that a proof that takes a `&&` apart (`arithmetic`'s bridge lemmas,
-- docs/proposals/omega.md §6.4) needn't load the sorting proofs.

--| `||` on `Bool`s: `False` is its unit, `True` absorbs, and it groups and
--| commutes.
theorem Bool.orFalse ∀ (b: Bool): (b ∨ False) = b := match b with | True | False => byComputing

theorem Bool.orTrue ∀ (b: Bool): (b ∨ True) = True := match b with | True | False => byComputing

theorem Bool.orAssoc ∀ (a b c: Bool): ((a ∨ b) ∨ c) = (a ∨ (b ∨ c)) := match a with | True | False => byComputing

theorem Bool.orComm ∀ (a b: Bool): (a ∨ b) = (b ∨ a) := match a, b with | True | False, True | False => byComputing

--| `&&` on `Bool`s groups and commutes, as `||` does.
theorem Bool.andAssoc ∀ (a b c: Bool): ((a ∧ b) ∧ c) = (a ∧ (b ∧ c)) := match a with | True | False => byComputing

theorem Bool.andComm ∀ (a b: Bool): (a ∧ b) = (b ∧ a) := match a, b with | True | False, True | False => byComputing

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
theorem Bool.toNatLeOne ∀ (b: Bool): Bool.toNat b ≤ 1 := match b with | True | False => byComputing

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
theorem Bool.andFalseMiddle ∀ (a c: Bool): (a && False && c) = False := match a with | True | False => byComputing

--| The `Bool` facts that lived in other files: the `Bool` lemmas from
--| `List/SortLemmas.sw`, and the theorems about nothing but `Bool` from
--| `Float`, `Float.Theory`, `Doc`, `Doc.Proofs` and `Quot`. They keep the
--| names they had there.
theorem Bool.toNatAddLeOne ∀ (b: Bool) (n: Nat) (h: Bool.toNat b + n ≤ 1): n ≤ 1 := match b, n with
  | False, n => h
  | True, Zero => byComputing

theorem Bool.andFalse ∀ (b: Bool): (b ∧ False) = False := match b with | True | False => byComputing

theorem Bool.andTrue ∀ (b: Bool): (b ∧ True) = b := match b with | True | False => byComputing

theorem Float.notNotAndOr ∀ (a b c d: Bool)
    (ha: a = False)
    (hb: b = False)
    (hd: d = True):
    (¬a ∧ ¬b ∧ (c ∨ d)) = True :=
  rewrite ha, hb, hd then match c with | True | False => byComputing

theorem Float.notNotAndNotAnd ∀ (a b c d: Bool)
    (ha: a = False)
    (hb: b = False)
    (hc: c = False)
    (hd: d = True):
    (¬a ∧ ¬b ∧ ¬c ∧ d) = True :=
  rewrite ha, hb, hc, hd

theorem Float.Theory.boolCases ∀ (b: Bool): (b = True) ∨ (b = False) := match b with
  | True => Inl byComputing
  | False => Inr byComputing

theorem Float.Theory.andFalseRight ∀ (b: Bool): (b ∧ False) = False := match b with | True | False => byComputing

theorem Float.Theory.andTrueRight ∀ (b: Bool): (b ∧ True) = b := match b with | True | False => byComputing

theorem Float.Theory.andSwap ∀ (a b: Bool): (a ∧ b) = (b ∧ a) := match a, b with
  | True | False, True | False => byComputing

theorem Float.Theory.orFalse ∀ (x y: Bool) (hx: x = False) (hy: y = False): (x ∨ y) = False := rewrite hx, hy

theorem Float.Theory.orLeftFalse ∀ (x y: Bool) (h: (x ∨ y) = False): x = False := match x with | False => byComputing

theorem Float.Theory.orRightFalse ∀ (x y: Bool) (h: (x ∨ y) = False): y = False := match y with
  | True => cases
  | False => byComputing

theorem Float.Theory.xorFalse ∀ (b: Bool): Bool.xor b False = b := match b with | True | False => byComputing

theorem Float.Theory.andFalseUp ∀ (a b c: Bool) (f: a = False → b = False) (k: (a ∧ c) = False): (b ∧ c) = False :=
  match a, b with
    | _, False => byComputing
    | False, True => Void.impossible (Bool.trueNotFalse (f byComputing))
    | True, True => k

theorem Float.Theory.xorFalseUp ∀ (a b c: Bool)
    (hc: c = False)
    (f: a = False → b = False)
    (k: Bool.xor a c = False):
    Bool.xor b c = False :=
  match a, b with
    | False, False => k
    | False, True => Void.impossible (Bool.trueNotFalse (f byComputing))
    | True, True => k
    | True, False => hc

theorem Float.Theory.xorComm ∀ (a b: Bool): Bool.xor a b = Bool.xor b a := match a, b with
  | True | False, True | False => byComputing

--| A disjunction that is false has a false right side.
theorem Doc.orFalseRight ∀ (left right: Bool) (plain: (left || right) = False): right = False :=
  match left, right, plain with | False, False, _ => byComputing

--| A flag is true or false.
theorem Doc.Proofs.trueOrFalse ∀ (flag: Bool): flag = True ∨ flag = False := match flag with
  | True => Inl byComputing
  | False => Inr byComputing

--| Booleans that are `True` together are equal.
theorem Quot.boolEq ∀ (b c: Bool) (toC: b = True → c = True) (toB: c = True → b = True): b = c := match b, c with
  | False, False => byComputing
  | False, True => toB byComputing
  | True, False => (toC byComputing).flipped
  | True, True => byComputing
