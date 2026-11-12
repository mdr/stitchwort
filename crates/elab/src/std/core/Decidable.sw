--| `Decidable`, its combinators, the decisions for `Nat`
--| and `Bool`, and the uniqueness of equality proofs on `Bool`.
-- Loaded with the core: `==`, `if h: x = y` and `auto` run on `Decidable`, and
-- `deriving (DecEq)` writes `Decidable.yes` and `Nat.equal` in full
-- (docs/proposals/prelude-slim.md §2.1).

-- Decisions

--| A decision whether `p` holds: a test, `holds`, with proofs that it is
--| right both ways. `sound` turns `holds = True` into a proof of `p`, and
--| `complete` a proof of `p` into `holds = True`; [`Decidable.refute`] gets
--| `¬p` from `holds = False`. A `==`, a plain `if` and `&&` on a decidable
--| proposition are its `holds`, and an `if h: p` splits on it. The proofs are
--| erased, so at run time a decision is its `Bool`.
--|
--| Write an instance test first, `{ holds = Nat.leq m n, sound = …, complete =
--| … }`, so that `holds` computes to the test even on unknowns; `if h: … then
--| Decidable.yes … else Decidable.no …` gives the same answers, but its
--| `holds` is stuck on the `if`.
-- (docs/proposals/decidable-record.md)
type Decidable (p: Prop) = {
  holds: Bool,
  sound: holds = True → p,
  complete: p → holds = True
}

--| What a decision's `Bool` says when it is `False`: `p` is refuted. Splitting
--| on the test (`match h: x < y with | True => … | False => …`) and then
--| calling `d.sound` or this on its equation `h` is how a proof gets the
--| evidence for `p` or against it.
theorem Decidable.refute [p: Prop] (d: Decidable p) (e: d.holds = False): ¬p :=
  h => Bool.falseNotTrue (Eq.trans (Eq.sym e) (d.complete h))

--| A refutation of `p` gives `holds d = False`: the converse of
--| [`Decidable.refute`], which has no field of its own.
-- In the core: the reader writes it for a fact `d.holds = False` built from
-- `¬p` (docs/proposals/bool-as-proposition.md §5.4, step 2).
theorem Decidable.toBoolOfNot [p: Prop] (d: Decidable p) (n: ¬p): Decidable.holds d = False :=
  match d with
    | { holds = True, sound = s, complete = c } => Void.exfalso (n (s rfl))
    | { holds = False, sound = s, complete = c } => rfl

--| The decision that `p` holds, from a proof of it, for a decision whose
--| answer is known.
def Decidable.yes [p: Prop] (h: p): Decidable p :=
  { holds = True, sound = e => h, complete = x => rfl }

--| The decision that `p` is false, from a refutation of it: [`Decidable.yes`]'s
--| partner.
def Decidable.no [p: Prop] (r: ¬p): Decidable p :=
  { holds = False, sound = e => Void.exfalso (Bool.falseNotTrue e), complete = h => Void.exfalso (r h) }

--| A decision of `q` from one of `p`, where each implies the other: the same
--| test, so `==` on a wrapper computes to `==` on what it wraps.
def Decidable.map [p q: Prop] (d: Decidable p) (forward: p → q) (backward: q → p): Decidable q :=
  { holds = d.holds, sound = h => forward (d.sound h), complete = x => d.complete (backward x) }

--| `ifYes` of the proof if the decision holds, `ifNo` of the refutation if not:
--| what `if h: p then a else b` means.
def Decidable.elim [p: Prop] [a: Type] (d: Decidable p) (ifYes: p → a) (ifNo: ¬p → a): a :=
  match e: d.holds with
    | True => ifYes (d.sound e)
    | False => ifNo (Decidable.refute d e)

--| An `if` gives equal results when its branches do, whichever way it goes.
-- The proofs that `decreasing` generates (`f.unfold`) take a step through an
-- `if` with these (docs/proposals/well-founded-recursion.md §6.2).
theorem Decidable.elimCong [p: Prop] [a: Type] (d: Decidable p) (y1 y2: p → a) (n1 n2: ¬p → a) (sameYes: ∀ (h: p) => y1 h = y2 h) (sameNo: ∀ (r: ¬p) => n1 r = n2 r): Decidable.elim d y1 n1 = Decidable.elim d y2 n2 :=
  match d with
    | { holds = True, sound = s, complete = c } => sameYes (s rfl)
    | { holds = False, sound = s, complete = c } => sameNo _

--| [`Decidable.elim`] for a proof: `if` with proofs as branches is this, and a
--| theorem with `decreasing (m1, m2)` makes its recursive calls through it.
-- (SW-1015)
-- (docs/proposals/well-founded-recursion.md, stage 3d)
theorem Decidable.elimProof [p: Prop] [a: Prop] (d: Decidable p) (ifYes: p → a) (ifNo: ¬p → a): a :=
  match e: d.holds with
    | True => ifYes (d.sound e)
    | False => ifNo (Decidable.refute d e)

--| An `if` equals `z` when both its branches do.
-- What `decreasing (m1, m2)` generates proves `f.unfold` with it
-- (docs/proposals/well-founded-recursion.md, stage 3d).
theorem Decidable.elimEq [p: Prop] [a: Type] (d: Decidable p) (y: p → a) (n: ¬p → a) (z: a) (yesEq: ∀ (h: p) => y h = z) (noEq: ∀ (r: ¬p) => n r = z): Decidable.elim d y n = z :=
  match d with
    | { holds = True, sound = s, complete = c } => yesEq (s rfl)
    | { holds = False, sound = s, complete = c } => noEq _

theorem Bool.ifThenElseCong [a: Type] (c: Bool) (t1 t2 e1 e2: Unit → a) (sameThen: ∀ (u: Unit) => t1 u = t2 u) (sameElse: ∀ (u: Unit) => e1 u = e2 u): Bool.ifThenElse c t1 e1 = Bool.ifThenElse c t2 e2 :=
  match c with
    | True => sameThen Trivial
    | False => sameElse Trivial

-- Decision procedures. `auto` and `if h: …` use those marked `instance`
-- (docs/proposals/interfaces.md §5.12); `=` is decided through `DecEq`
-- instead (below), and the procedures for `=` here are what its instances
-- are made of.

--| Decides whether a boolean is `True`: the test is the boolean itself.
def Bool.decTrue (b: Bool): Decidable (b = True) := { holds = b, sound = h => h, complete = h => h }

--| Decides whether two numbers are equal by [`Nat.equal`], which runs
--| natively on numbers however big.
def Nat.decEq (m: Nat) (n: Nat): Decidable (m = n) := {
  holds = Nat.equal m n,
  sound = h => Nat.equalSound m n h,
  complete = h => J (n' e => Nat.equal m n' = True) (Nat.equalRefl m) h
}

theorem Bool.trueNotFalse: True ≠ False
  | p => Bool.falseNotTrue (Eq.sym p)

--| Decides whether two booleans are equal.
def Bool.decEq: (a: Bool) → (b: Bool) → Decidable (a = b)
  | False, False => Decidable.yes rfl
  | False, True => Decidable.no Bool.falseNotTrue
  | True, False => Decidable.no Bool.trueNotFalse
  | True, True => Decidable.yes rfl

--| What [`Decidable.not`]'s test says when it is `True`.
theorem Decidable.notSound [p: Prop] (d: Decidable p) (h: Bool.not d.holds = True): ¬p :=
  match d with
    | { holds = False, sound = s, complete = c } => x => Bool.falseNotTrue (c x)

--| What [`Decidable.not`]'s test says when `¬p` holds.
theorem Decidable.notComplete [p: Prop] (d: Decidable p) (r: ¬p): Bool.not d.holds = True :=
  match d with
    | { holds = True, sound = s, complete = c } => Void.exfalso (r (s rfl))
    | { holds = False, sound = s, complete = c } => rfl

--| `!p` is decided from a decision of `p`: its test is `not` of `p`'s.
instance Decidable.not [p: Prop] (d: Decidable p): Decidable (¬p) :=
  { holds = Bool.not d.holds, sound = Decidable.notSound d, complete = Decidable.notComplete d }

--| What [`Decidable.and`]'s test says when it is `True`.
theorem Decidable.andSound [p q: Prop] (dp: Decidable p) (dq: Decidable q) (h: Bool.ifThenElse dp.holds (u => dq.holds) (u => False) = True): p ∧ q :=
  match dp with
    | { holds = True, sound = s, complete = c } => Both (s rfl) (dq.sound h)

--| What [`Decidable.and`]'s test says when `p ∧ q` holds.
theorem Decidable.andComplete [p q: Prop] (dp: Decidable p) (dq: Decidable q) (h: p ∧ q): Bool.ifThenElse dp.holds (u => dq.holds) (u => False) = True :=
  match dp with
    | { holds = True, sound = s, complete = c } => dq.complete (And.right h)
    | { holds = False, sound = s, complete = c } => c (And.left h)

--| `p && q` is decided from decisions of each side: its test is the `Bool`
--| `&&` of theirs. Both are worked out before this is called (an argument
--| is), while [`Decidable.andThen`] decides `q` only once `p` holds.
instance Decidable.and [p q: Prop] (dp: Decidable p) (dq: Decidable q): Decidable (p ∧ q) := {
  holds = Bool.ifThenElse dp.holds (u => dq.holds) (u => False),
  sound = Decidable.andSound dp dq,
  complete = Decidable.andComplete dp dq
}

--| What [`Decidable.andThen`]'s test says when it is `True`.
theorem Decidable.andThenSound [p q: Prop] (dp: Decidable p) (dq: Unit → Decidable q) (h: Bool.ifThenElse dp.holds (u => (dq Trivial).holds) (u => False) = True): p ∧ q :=
  match dp with
    | { holds = True, sound = s, complete = c } => Both (s rfl) ((dq Trivial).sound h)

--| What [`Decidable.andThen`]'s test says when `p ∧ q` holds.
theorem Decidable.andThenComplete [p q: Prop] (dp: Decidable p) (dq: Unit → Decidable q) (h: p ∧ q): Bool.ifThenElse dp.holds (u => (dq Trivial).holds) (u => False) = True :=
  match dp with
    | { holds = True, sound = s, complete = c } => (dq Trivial).complete (And.right h)
    | { holds = False, sound = s, complete = c } => c (And.left h)

--| `p && q` decided as `if p && q` decides it: `q` only once `p` holds, so
--| `q`'s decision is passed unevaluated, and the test is the `Bool` `&&`. An
--| `if` on `p && q` whose branches use its proof (`if b != 0 && c != 0 then a
--| % b`) is decided by this.
def Decidable.andThen [p q: Prop] (dp: Decidable p) (dq: Unit → Decidable q): Decidable (p ∧ q) := {
  holds = Bool.ifThenElse dp.holds (u => (dq Trivial).holds) (u => False),
  sound = Decidable.andThenSound dp dq,
  complete = Decidable.andThenComplete dp dq
}

--| What [`Decidable.or`]'s test says when it is `True`.
theorem Decidable.orSound [p q: Prop] (dp: Decidable p) (dq: Decidable q) (h: Bool.ifThenElse dp.holds (u => True) (u => dq.holds) = True): p ∨ q :=
  match dp with
    | { holds = True, sound = s, complete = c } => Inl (s rfl)
    | { holds = False, sound = s, complete = c } => Inr (dq.sound h)

--| What [`Decidable.or`]'s test says when `p ∨ q` holds.
theorem Decidable.orComplete [p q: Prop] (dp: Decidable p) (dq: Decidable q) (h: p ∨ q): Bool.ifThenElse dp.holds (u => True) (u => dq.holds) = True :=
  match dp, h with
    | { holds = True, sound = s, complete = c }, h => rfl
    | { holds = False, sound = s, complete = c }, Inl a => Void.exfalso (Bool.falseNotTrue (c a))
    | { holds = False, sound = s, complete = c }, Inr b => dq.complete b

--| `p || q` is decided from decisions of each side, both worked out first, as
--| for [`Decidable.and`]: its test is the `Bool` `||` of theirs.
instance Decidable.or [p q: Prop] (dp: Decidable p) (dq: Decidable q): Decidable (p ∨ q) := {
  holds = Bool.ifThenElse dp.holds (u => True) (u => dq.holds),
  sound = Decidable.orSound dp dq,
  complete = Decidable.orComplete dp dq
}

--| `m <= n` is decided by computing `Nat.leq m n`.
instance Nat.decLessEq (m: Nat) (n: Nat): Decidable (m ≤ n) := { holds = Nat.leq m n, sound = h => h, complete = h => h }

--| `m < n` is decided by computing `Nat.leq (m + 1) n`.
instance Nat.decLessThan (m: Nat) (n: Nat): Decidable (m < n) := { holds = Nat.leq (Succ m) n, sound = h => h, complete = h => h }

--| Hedberg's argument, for any type whose equality has a decision: `canon`
--| turns any proof of `x = y` into the one the decision gives, ignoring which
--| proof it was given.
def Decidable.canon [x y: a] (dec: Decidable (x = y)) (h: x = y): x = y :=
  match e: dec.holds with
    | True => dec.sound e
    | False => Void.exfalso (Decidable.refute dec e h)

--| Every proof of `x = y` has the same canonical form.
theorem Decidable.canonConst [x y: a] (dec: Decidable (x = y)) (p q: x = y): Decidable.canon dec p = Decidable.canon dec q :=
  match dec with
    | { holds = True, sound = s, complete = c } => rfl
    | { holds = False, sound = s, complete = c } => Void.exfalso (Bool.falseNotTrue (c p))

theorem Decidable.symThenSelf [x y: a] (q: x = y): rfl = Eq.trans (Eq.sym q) q := J (y' q' => rfl = Eq.trans (Eq.sym q') q') rfl q

--| Every proof can be recovered from its canonical one.
theorem Decidable.fromCanon (decide: (x: a) → (y: a) → Decidable (x = y)) (x: a) (y: a) (p: x = y):
    p = Eq.trans (Eq.sym (Decidable.canon (decide x x) rfl)) (Decidable.canon (decide x y) p) :=
  J (y' p' => p' = Eq.trans (Eq.sym (Decidable.canon (decide x x) rfl)) (Decidable.canon (decide x y') p'))
    (Decidable.symThenSelf (Decidable.canon (decide x x) rfl)) p

--| Proofs of an equation in a type with decidable equality are unique.
theorem Decidable.uniqueEq (decide: (x: a) → (y: a) → Decidable (x = y)) (x: a) (y: a) (p: x = y) (q: x = y): p = q :=
  J (z e => p = z)
    (J (r e => p = Eq.trans (Eq.sym (Decidable.canon (decide x x) rfl)) r)
      (Decidable.fromCanon decide x y p) (Decidable.canonConst (decide x y) p q))
    (J (z e => z = q) rfl (Decidable.fromCanon decide x y q))

--| Proofs that two booleans are equal are unique. This is Hedberg's argument,
--| which works for any type with decidable equality: [`Bool.canon`] turns any proof
--| of `x = y` into one chosen by [`Bool.decEq`], so it ignores which proof it was
--| given, and every proof can be recovered from its canonical one.
def Bool.canon [x y: Bool] (dec: Decidable (x = y)) (h: x = y): x = y :=
  match e: dec.holds with
    | True => dec.sound e
    | False => Void.exfalso (Decidable.refute dec e h)

theorem Bool.canonConst [x y: Bool] (d: Decidable (x = y)) (p q: x = y):
    Bool.canon d p = Bool.canon d q :=
  match d with
    | { holds = True, sound = s, complete = c } => rfl
    | { holds = False, sound = s, complete = c } => Void.exfalso (Bool.falseNotTrue (c p))

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
instance Void.dec: Decidable Void := { holds = False, sound = e => Void.exfalso (Bool.falseNotTrue e), complete = none => Void.exfalso none }

--| `Unit` is decided: it is true. `List.Distinct` of a list written out
--| computes to `… ∧ Unit`, and this is the last.
instance Unit.dec: Decidable Unit := { holds = True, sound = e => Trivial, complete = u => rfl }
