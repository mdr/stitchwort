--| `Decidable`, its combinators, the decisions for `Nat`
--| and `Bool`, and the uniqueness of equality proofs on `Bool`.
-- Loaded with the core: `==`, `if h: x = y` and `auto` run on `Decidable`, and
-- `deriving (DecEq)` writes `Decidable.Yes` and `Nat.equal` in full
-- (docs/proposals/prelude-slim.md §2.1).

-- Decisions

--| Either a proof of `p` or a proof that `p` is false. Whether it's `Yes` or
--| `No` exists at runtime; the proofs inside are erased.
type Decidable (p: Prop): Type =
  | Yes (proof: p)
  | No (refutation: ¬p)

--| `Decidable.IsYes d` is `Unit` (provable) exactly when `d` is `Yes`.
def Decidable.IsYes: (d: Decidable p) → Prop
  | Yes h => Unit
  | No r => Void

--| How `auto` turns a decision into a proof: `Decidable.fromYes d Trivial` only checks
--| when `d` computes to `Yes`.
def Decidable.fromYes: [p: Prop] → (d: Decidable p) → (yes: Decidable.IsYes d) → p
  | Yes h, u => h
  | No r, u => Void.exfalso u

--| `a == b` is `Decidable.toBool d`, for a decision procedure `d` for `a = b`.
def Decidable.toBool: [p: Prop] → (d: Decidable p) → Bool
  | Yes h => True
  | No r => False

--| The decision that `p` holds, from a proof of it. Write `Decidable.yes h`
--| rather than the constructor: the type of a decision is going to change, and
--| this and [`Decidable.no`] are then the only things to change.
def Decidable.yes [p: Prop] (h: p): Decidable p := Yes h

--| The decision that `p` is false, from a refutation of it: [`Decidable.yes`]'s
--| partner.
def Decidable.no [p: Prop] (r: ¬p): Decidable p := No r

--| The `Bool` a decision stands for: `True` when it says yes. A `==`, a plain
--| `if` and `&&` on a decidable proposition are this `Bool`. Its facts are
--| [`Decidable.sound`], [`Decidable.refute`] and [`Decidable.toBoolOf`].
def Decidable.does [p: Prop] (d: Decidable p): Bool := Decidable.toBool d

--| `yes` of the proof if the decision is `Yes`, `no` of the refutation if it is `No`: what `if h: p then a else b` means.
def Decidable.elim: [p: Prop] → [a: Type] → (d: Decidable p) → (ifYes: p → a) → (ifNo: ¬p → a) → a
  | Yes h, yes, no => yes h
  | No r, yes, no => no r

--| An `if` gives equal results when its branches do, whichever way it goes.
-- The proofs that `decreasing` generates (`f.unfold`) take a step through an
-- `if` with these (docs/proposals/well-founded-recursion.md §6.2).
theorem Decidable.elimCong [p: Prop] [a: Type] (d: Decidable p) (y1 y2: p → a) (n1 n2: ¬p → a) (sameYes: ∀ (h: p) => y1 h = y2 h) (sameNo: ∀ (r: ¬p) => n1 r = n2 r): Decidable.elim d y1 n1 = Decidable.elim d y2 n2 :=
  match d with
    | Yes h => sameYes h
    | No r => sameNo r

--| [`Decidable.elim`] for a proof: `if` with proofs as branches is this, and a
--| theorem with `decreasing (m1, m2)` makes its recursive calls through it.
-- (SW-1015)
-- (docs/proposals/well-founded-recursion.md, stage 3d)
theorem Decidable.elimProof [p: Prop] [a: Prop] (d: Decidable p) (ifYes: p → a) (ifNo: ¬p → a): a :=
  match d with
    | Yes h => ifYes h
    | No r => ifNo r

--| An `if` equals `z` when both its branches do.
-- What `decreasing (m1, m2)` generates proves `f.unfold` with it
-- (docs/proposals/well-founded-recursion.md, stage 3d).
theorem Decidable.elimEq [p: Prop] [a: Type] (d: Decidable p) (y: p → a) (n: ¬p → a) (z: a) (yesEq: ∀ (h: p) => y h = z) (noEq: ∀ (r: ¬p) => n r = z): Decidable.elim d y n = z :=
  match d with
    | Yes h => yesEq h
    | No r => noEq r

theorem Bool.ifThenElseCong [a: Type] (c: Bool) (t1 t2 e1 e2: Unit → a) (sameThen: ∀ (u: Unit) => t1 u = t2 u) (sameElse: ∀ (u: Unit) => e1 u = e2 u): Bool.ifThenElse c t1 e1 = Bool.ifThenElse c t2 e2 :=
  match c with
    | True => sameThen Trivial
    | False => sameElse Trivial

--| An `if` that decides `p` is the plain `if` on `Decidable.toBool d` when its
--| branches agree with the plain ones.
-- `f.unfold` of a `decreasing` definition shows the plain `if` where only the
-- recursive calls' proofs used the condition, and is proved with this and
-- [`Bool.elimDecTrueIf`] (docs/proposals/decreasing-with-hypothesis.md).
theorem Decidable.elimIf [p: Prop] [a: Type] (d: Decidable p) (y: p → a) (n: ¬p → a) (t e: Unit → a) (sameYes: ∀ (h: p) => y h = t Trivial) (sameNo: ∀ (r: ¬p) => n r = e Trivial): Decidable.elim d y n = Bool.ifThenElse (Decidable.toBool d) t e :=
  match d with
    | Yes h => sameYes h
    | No r => sameNo r

--| [`Decidable.elimIf`] for a `Bool` condition `c`, decided by `Bool.decTrue c`
--| (and for a comparison, whose decision is that).
theorem Bool.elimDecTrueIf [a: Type] (c: Bool) (y: c = True → a) (n: ¬(c = True) → a) (t e: Unit → a) (sameYes: ∀ (h: c = True) => y h = t Trivial) (sameNo: ∀ (r: ¬(c = True)) => n r = e Trivial): Decidable.elim (Bool.decTrue c) y n = Bool.ifThenElse c t e :=
  match c with
    | True => sameYes rfl
    | False => sameNo Bool.falseNotTrue

-- Decision procedures. `auto` and `if h: …` use those marked `instance`
-- (docs/proposals/interfaces.md §5.12); `=` is decided through `DecEq`
-- instead (below), and the procedures for `=` here are what its instances
-- are made of.
-- `Decidable …`.

--| Decides whether a boolean is `True`.
def Bool.decTrue: (b: Bool) → Decidable (b = True)
  | True => Yes rfl
  | False => No Bool.falseNotTrue

--| A decision from what [`Nat.equal`] says.
def Nat.decEqFrom (m: Nat) (n: Nat): (b: Bool) → (h: Nat.equal m n = b) → Decidable (m = n)
  | True, h => Yes (Nat.equalSound m n h)
  | False, h => No (Nat.equalFalse m n h)

--| For two numbers this computes `Yes rfl` or `No (Nat.equalFalse m n rfl)`,
--| and the native gives exactly that, however big they are. It matches on both
--| numbers so it waits until they're known, rather than unfolding around an
--| unknown one.
-- (Recursing on both numbers one step at a time would build a refutation as
-- deep as the smaller number.)
def Nat.decEq: (m: Nat) → (n: Nat) → Decidable (m = n)
  | Zero, Zero => Yes rfl
  | Zero, Succ n => No (Nat.equalFalse 0 (Succ n) rfl)
  | Succ m, Zero => No (Nat.equalFalse (Succ m) 0 rfl)
  | Succ m, Succ n => Nat.decEqFrom (Succ m) (Succ n) (Nat.equal m n) rfl

theorem Bool.trueNotFalse: True ≠ False
  | p => Bool.falseNotTrue (Eq.sym p)

--| Decides whether two booleans are equal.
def Bool.decEq: (a: Bool) → (b: Bool) → Decidable (a = b)
  | False, False => Yes rfl
  | False, True => No Bool.falseNotTrue
  | True, False => No Bool.trueNotFalse
  | True, True => Yes rfl

--| `!p` is decided from a decision of `p`.
instance Decidable.not: [p: Prop] → Decidable p → Decidable (¬p)
  | Yes h => No (n => n h)
  | No r => Yes r

--| `p && q` is decided from decisions of each side. Both are worked out before
--| this is called, so `if h: p && q` decides `q` even when `p` is false
--| (`if p && q`, without a name, doesn't).
instance Decidable.and: [p q: Prop] → Decidable p → Decidable q → Decidable (p ∧ q)
  | Yes a, Yes b => Yes (Both a b)
  | Yes a, No r => No (h => r (And.right h))
  | No r, d => No (h => r (And.left h))

--| `p ∧ q` decided from a decision of `q` and a proof of `p`.
def Decidable.andYes: [p q: Prop] → (dq: Decidable q) → (hp: p) → Decidable (p ∧ q)
  | Yes b, a => Yes (Both a b)
  | No r, a => No (h => r (And.right h))

--| `p && q` decided as `if p && q` decides it: `q` only once `p` holds, so
--| `q`'s decision is passed unevaluated. An `if` on `p && q` whose branches use
--| its proof (`if b != 0 && c != 0 then a % b`) is decided by this.
def Decidable.andThen: [p q: Prop] → (dp: Decidable p) → (dq: Unit → Decidable q) → Decidable (p ∧ q)
  | Yes a, dq => Decidable.andYes (dq Trivial) a
  | No r, dq => No (h => r (And.left h))

--| `p || q` is decided from decisions of each side, both worked out first, as for [`Decidable.and`].
instance Decidable.or: [p q: Prop] → Decidable p → Decidable q → Decidable (p ∨ q)
  | Yes a, d => Yes (Inl a)
  | No r, Yes b => Yes (Inr b)
  | No r, No s => No (Or.neither r s)

--| `m <= n` is decided by computing `Nat.leq m n`.
instance Nat.decLessEq (m: Nat) (n: Nat): Decidable (m ≤ n) := Bool.decTrue (Nat.leq m n)

--| `m < n` is decided by computing `Nat.leq (m + 1) n`.
instance Nat.decLessThan (m: Nat) (n: Nat): Decidable (m < n) := Bool.decTrue (Nat.leq (Succ m) n)

--| Proofs that two booleans are equal are unique. This is Hedberg's argument,
--| which works for any type with decidable equality: [`Bool.canon`] turns any proof
--| of `x = y` into one chosen by [`Bool.decEq`], so it ignores which proof it was
--| given, and every proof can be recovered from its canonical one.
def Bool.canon: [x y: Bool] → (dec: Decidable (x = y)) → (h: x = y) → x = y
  | Yes e, p => e
  | No r, p => Void.exfalso (r p)

theorem Bool.canonConst [x y: Bool] (d: Decidable (x = y)) (p q: x = y):
    Bool.canon d p = Bool.canon d q :=
  match d with
    | Yes e => rfl
    | No r => Void.exfalso (r p)

theorem Bool.symThenSelf [x y: Bool] (q: x = y): rfl = Eq.trans (Eq.sym q) q := J (y' q' => rfl = Eq.trans (Eq.sym q') q') rfl q

theorem Bool.fromCanon (x: Bool) (y: Bool) (p: x = y):
    p = Eq.trans (Eq.sym (Bool.canon (Bool.decEq x x) rfl)) (Bool.canon (Bool.decEq x y) p) :=
  J (y' p' => p' = Eq.trans (Eq.sym (Bool.canon (Bool.decEq x x) rfl)) (Bool.canon (Bool.decEq x y') p'))
    (Bool.symThenSelf (Bool.canon (Bool.decEq x x) rfl)) p

theorem Bool.uniqueEq (x: Bool) (y: Bool) (p: x = y) (q: x = y): p = q :=
  J (z e => p = z)
    (J (r e => p = Eq.trans (Eq.sym (Bool.canon (Bool.decEq x x) rfl)) r)
      (Bool.fromCanon x y p) (Bool.canonConst (Bool.decEq x y) p q))
    (J (z e => z = q) rfl (Bool.fromCanon x y q))

--| `Void` is decided: it is false. Membership in a list written out computes
--| to `y = x || … || Void`, decided one disjunct at a time, and this is the
--| last.
-- In the core, so `auto` never depends on what is loaded (D58).
instance Void.dec: Decidable Void := No (none => none)

--| `Unit` is decided: it is true. `List.Distinct` of a list written out
--| computes to `… ∧ Unit`, and this is the last.
instance Unit.dec: Decidable Unit := Yes Trivial
