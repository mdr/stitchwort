--| Equality lemmas ([`Eq.cong`], [`Eq.cong2`], [`Eq.sym`], [`Eq.trans`])
--| and the facts that different constructors are different.
-- Loaded with the core: `calc` and `deriving` write `Eq.sym` and `Eq.trans` in
-- full, and every decision procedure after this uses them
-- (docs/proposals/prelude-slim.md §2.1).

--| Equality lemmas, all built from `J`.

theorem Eq.cong (f: a → b) [x y: a] (p: x = y): f x = f y := J (y' p' => f x = f y') rfl p

--| Congruence in two arguments: equal arguments give equal results,
--| `Eq.cong2 Nat.add p q: Nat.add a b = Nat.add a2 b2` from `p: a = a2` and
--| `q: b = b2`.
--| For one argument of a function of several, use `Eq.cong` with the
--| others fixed: `Eq.cong (t => f t y) p`.
theorem Eq.cong2 (f: a → b → c) [x1 x2: a] [y1 y2: b] (p: x1 = x2) (q: y1 = y2): f x1 y1 = f x2 y2 :=
  J (x' p' => f x1 y1 = f x' y2) (Eq.cong (f x1) q) p

theorem Eq.sym [x y: a] (p: x = y): y = x := J (y' p' => y' = x) rfl p

theorem Eq.trans [x y z: a] (p: x = y) (q: y = z): x = z := J (z' q' => x = z') p q

--| Moves a fact along an equation: from `h: x = y` and a fact about `x`, the
--| same fact about `y`. `motive` says what the fact is about, as a function
--| of the value: `Eq.subst (n => n < 10) h fact`. Use it in place of `J` when
--| `rewrite` runs out of budget; unlike `J`'s motive it takes no proof
--| argument, and the equation comes before the fact. Elaboration cannot
--| find `motive` from the types (it would need higher-order unification), so
--| it is always written out.
theorem Eq.subst (motive: a → Prop) [x y: a] (h: x = y) (fact: motive x): motive y := J (y' p' => motive y') fact h

-- Different constructors are different. Each proof transports along the
-- equation into a family that's `Unit` at one constructor and `Void` at the other.

--| `Unit` (true) for 0 and `Void` (false) for any other number: how `0 ≠ n + 1` is proved.
def Nat.IsZero: (n: Nat) → Prop
  | Zero => Unit
  | Succ n => Void

theorem Nat.zeroNotSucc (n: Nat): 0 ≠ Succ n
  | p => J (y q => Nat.IsZero y) Trivial p

theorem Nat.succNotZero (n: Nat): Succ n ≠ 0
  | p => Nat.zeroNotSucc n (Eq.sym p)

theorem Nat.succInjective [m: Nat] [n: Nat] (p: Succ m = Succ n): m = n := Eq.cong Nat.pred p

--| `Unit` (true) for `False` and `Void` (false) for `True`: how `False ≠ True` is proved.
def Bool.IsFalse: (b: Bool) → Prop
  | False => Unit
  | True => Void

--| `False` isn't `True`. Written as an absurd pattern: an equation between two
--| different constructors has no proofs, so `()` matches it with nothing to return.
theorem Bool.falseNotTrue: False ≠ True
  | ()

--| Whether two numbers are equal, as a `Bool`.
@[tailrec]
def Nat.equal: (m: Nat) → (n: Nat) → Bool
  | Zero, Zero => True
  | Zero, Succ n => False
  | Succ m, Zero => False
  | Succ m, Succ n => Nat.equal m n

theorem Nat.equalRefl (n: Nat): Nat.equal n n = True :=
  match n with
    | Zero => rfl
    | Succ n => Nat.equalRefl n

--| Numbers that [`Nat.equal`] says are equal are equal.
theorem Nat.equalSound (m n: Nat) (h: Nat.equal m n = True): m = n :=
  match m, n with
    | Zero, Zero => rfl
    | Succ m, Succ n => Eq.cong Succ (Nat.equalSound m n h)

--| Numbers that [`Nat.equal`] says differ are different.
theorem Nat.equalFalse (m: Nat) (n: Nat) (h: Nat.equal m n = False): m ≠ n
  | p => Bool.falseNotTrue (Eq.trans (Eq.sym h) (J (y q => Nat.equal m y = True) (Nat.equalRefl m) p))

--| `Nat.equal` (what `m == n` is on `Nat`) reads as `m = n`, and as `m ≠ n`
--| when it is `False`.
@[reading]
theorem Nat.equalReads (m n: Nat): Nat.equal m n ↔ m = n := {
  forward = Nat.equalSound m n,
  backward = h => J (y q => Nat.equal m y = True) (Nat.equalRefl m) h
}

@[reading]
theorem Nat.equalReadsFalse (m n: Nat): Nat.equal m n = False ↔ m ≠ n := {
  forward = Nat.equalFalse m n,
  backward = h =>
    match c: Nat.equal m n with
      | True => Void.exfalso (h (Nat.equalSound m n c))
      | False => rfl
}

--| `Nat.leq m n` (what `m <= n` is on `Nat`, and `m < n` and the other
--| comparisons through it) reads as `m ≤ n`. The proposition is itself defined
--| as this test being `True`, so the reading is the identity.
@[reading]
theorem Nat.leqReads (m n: Nat): Nat.leq m n ↔ Nat.LessEq m n := { forward = h => h, backward = h => h }

--| `Nat.leq m n` is `False` exactly when `n` is below `m`: `(x <= y) = False`
--| reads as `y < x`, and `(x < y) = False` as `y < x + 1`, which is `y ≤ x`.
@[reading]
theorem Nat.leqReadsFalse (m n: Nat): Nat.leq m n = False ↔ Nat.LessThan n m :=
  match m, n with
    | Zero, n => { forward = h => Void.exfalso (Bool.trueNotFalse h), backward = h => Void.exfalso (Bool.falseNotTrue h) }
    | Succ m, Zero => { forward = h => rfl, backward = h => rfl }
    | Succ m, Succ n => { forward = h => Iff.forward (Nat.leqReadsFalse m n) h, backward = h => Iff.backward (Nat.leqReadsFalse m n) h }

--| `&&`, `||` and `not` read as the connectives
--| (docs/proposals/bool-as-proposition.md §5): a fact `(a && b) = True` is
--| taken apart and built like `a ∧ b` (`match h with | Both l r`), and
--| `h.read` is `a ∧ b`. Each `= False` has its own reading.
@[reading]
theorem Bool.andReads (a b: Bool): (a && b) = True ↔ a ∧ b :=
  match a with
    | True => { forward = h => Both rfl h, backward = h => h.right }
    | False => { forward = h => Void.exfalso (Bool.falseNotTrue h), backward = h => h.left }

@[reading]
theorem Bool.andReadsFalse (a b: Bool): (a && b) = False ↔ a = False ∨ b = False :=
  match a with
    | True => {
      forward = h => Inr h,
      backward = h =>
        match h with
          | Inl t => Void.exfalso (Bool.falseNotTrue (Eq.sym t))
          | Inr f => f
    }
    | False => { forward = h => Inl rfl, backward = h => rfl }

@[reading]
theorem Bool.orReads (a b: Bool): (a || b) = True ↔ a ∨ b :=
  match a with
    | True => { forward = h => Inl rfl, backward = h => rfl }
    | False => {
      forward = h => Inr h,
      backward = h =>
        match h with
          | Inl f => Void.exfalso (Bool.falseNotTrue f)
          | Inr t => t
    }

@[reading]
theorem Bool.orReadsFalse (a b: Bool): (a || b) = False ↔ a = False ∧ b = False :=
  match a with
    | True => { forward = h => Void.exfalso (Bool.falseNotTrue (Eq.sym h)), backward = h => h.left }
    | False => { forward = h => Both rfl h, backward = h => h.right }

@[reading]
theorem Bool.notReads (a: Bool): Bool.not a = True ↔ a = False :=
  match a with
    | True => {
      forward = h => Void.exfalso (Bool.falseNotTrue h),
      backward = h => Void.exfalso (Bool.falseNotTrue (Eq.sym h))
    }
    | False => { forward = h => rfl, backward = h => rfl }

@[reading]
theorem Bool.notReadsFalse (a: Bool): Bool.not a = False ↔ a = True :=
  match a with
    | True => { forward = h => rfl, backward = h => rfl }
    | False => {
      forward = h => Void.exfalso (Bool.falseNotTrue (Eq.sym h)),
      backward = h => Void.exfalso (Bool.falseNotTrue h)
    }
