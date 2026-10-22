-- core/Decidable.sw. `Decidable`, its combinators, the decisions for `Nat`
-- and `Bool`, and the uniqueness of equality proofs on `Bool`. Loaded with
-- the core: `==`, `if h: x = y` and `auto` run on `Decidable`, and `deriving
-- (DecEq)` writes `Decidable.Yes` and `Nat.equal` in full
-- (docs/proposals/prelude-slim.md §2.1).

-- Decisions

-- Either a proof of `p` or a proof that `p` is false. Whether it's `Yes` or
-- `No` exists at runtime; the proofs inside are erased.
type Decidable (p: Prop): Type =
  | Yes (proof: p)
  | No (refutation: Not p)

-- `Decidable.IsYes d` is `Unit` (provable) exactly when `d` is `Yes`.
def Decidable.IsYes: Decidable p -> Prop
  | Yes h => Unit
  | No r  => Void

-- How `auto` turns a decision into a proof: `Decidable.fromYes d Trivial` only checks
-- when `d` computes to `Yes`.
def Decidable.fromYes: [p: Prop] -> (d: Decidable p) -> Decidable.IsYes d -> p
  | Yes h, u => h
  | No r,  u => Void.exfalso u

-- `a == b` is `Decidable.toBool d`, for a decision procedure `d` for `a = b`.
def Decidable.toBool: [p: Prop] -> Decidable p -> Bool
  | Yes h => True
  | No r  => False

-- `if h: p then a else b`
def Decidable.elim: [p: Prop] -> [a: Type] -> Decidable p -> (p -> a) -> (Not p -> a) -> a
  | Yes h, yes, no => yes h
  | No r,  yes, no => no r

-- An `if` gives equal results when its branches do, whichever way it goes.
-- The proofs that `decreasing` generates (`f.unfold`) take a step through an
-- `if` with these (docs/proposals/well-founded-recursion.md §6.2).
theorem Decidable.elimCong: [p: Prop] -> [a: Type] -> (d: Decidable p) -> (y1: p -> a) -> (y2: p -> a) -> (n1: Not p -> a) -> (n2: Not p -> a) -> ((h: p) -> y1 h = y2 h) -> ((r: Not p) -> n1 r = n2 r) -> Decidable.elim d y1 n1 = Decidable.elim d y2 n2
  | Yes h, y1, y2, n1, n2, ey, en => ey h
  | No r,  y1, y2, n1, n2, ey, en => en r

theorem Bool.ifThenElseCong: [a: Type] -> (c: Bool) -> (t1: Unit -> a) -> (t2: Unit -> a) -> (e1: Unit -> a) -> (e2: Unit -> a) -> ((u: Unit) -> t1 u = t2 u) -> ((u: Unit) -> e1 u = e2 u) -> Bool.ifThenElse c t1 e1 = Bool.ifThenElse c t2 e2
  | True,  t1, t2, e1, e2, et, ee => et Trivial
  | False, t1, t2, e1, e2, et, ee => ee Trivial

-- Decision procedures. `auto` and `if h: …` use those marked `instance`
-- (docs/proposals/interfaces.md §5.12); `=` is decided through `DecEq`
-- instead (below), and the procedures for `=` here are what its instances
-- are made of.
-- `Decidable …`.

def Bool.decTrue: (b: Bool) -> Decidable (b = True)
  | True  => Yes rfl
  | False => No Bool.falseNotTrue

-- A decision from what `Nat.equal` says.
def Nat.decEqFrom (m: Nat) (n: Nat): (b: Bool) -> Nat.equal m n = b -> Decidable (m = n)
  | True,  h => Yes (Nat.equalSound m n h)
  | False, h => No (Nat.equalFalse m n h)

-- For two numbers this computes `Yes rfl` or `No (Nat.equalFalse m n rfl)`, and the
-- native gives exactly that, however big they are. (Recursing on both numbers
-- one step at a time would build a refutation as deep as the smaller number.)
-- It matches on both numbers so it waits until they're known, rather than
-- unfolding around an unknown one.
def Nat.decEq: (m: Nat) -> (n: Nat) -> Decidable (m = n)
  | Zero,   Zero   => Yes rfl
  | Zero,   Succ n => No (Nat.equalFalse 0 (Succ n) rfl)
  | Succ m, Zero   => No (Nat.equalFalse (Succ m) 0 rfl)
  | Succ m, Succ n => Nat.decEqFrom (Succ m) (Succ n) (Nat.equal m n) rfl

theorem Bool.trueNotFalse: Not (True = False)
  | p => Bool.falseNotTrue (Eq.sym p)

def Bool.decEq: (a: Bool) -> (b: Bool) -> Decidable (a = b)
  | False, False => Yes rfl
  | False, True  => No Bool.falseNotTrue
  | True,  False => No Bool.trueNotFalse
  | True,  True  => Yes rfl

instance Decidable.not: [p: Prop] -> Decidable p -> Decidable (Not p)
  | Yes h => No (n => n h)
  | No r  => Yes r

-- `p && q` and `p || q` are decided from decisions of each side. Both are
-- worked out before these are called, so `if h: p && q` decides `q` even when
-- `p` is false (`if p && q`, without a name, doesn't).
instance Decidable.and: [p q: Prop] -> Decidable p -> Decidable q -> Decidable (And p q)
  | Yes a, Yes b => Yes (Both a b)
  | Yes a, No r  => No (h => r (And.right h))
  | No r,  d     => No (h => r (And.left h))

instance Decidable.or: [p q: Prop] -> Decidable p -> Decidable q -> Decidable (Or p q)
  | Yes a, d     => Yes (Inl a)
  | No r,  Yes b => Yes (Inr b)
  | No r,  No s  => No (Or.neither r s)

instance Nat.decLessEq (m: Nat) (n: Nat): Decidable (m <= n) := Bool.decTrue (Nat.leq m n)

instance Nat.decLessThan (m: Nat) (n: Nat): Decidable (m < n) := Bool.decTrue (Nat.leq (Succ m) n)

-- Proofs that two booleans are equal are unique. This is Hedberg's argument,
-- which works for any type with decidable equality: `Bool.canon` turns any proof
-- of `x = y` into one chosen by `Bool.decEq`, so it ignores which proof it was
-- given, and every proof can be recovered from its canonical one.
def Bool.canon: [x y: Bool] -> Decidable (x = y) -> x = y -> x = y
  | Yes e, p => e
  | No r,  p => Void.exfalso (r p)

theorem Bool.canonConst: [x y: Bool] -> (d: Decidable (x = y)) -> (p: x = y) -> (q: x = y) ->
    Bool.canon d p = Bool.canon d q
  | Yes e, p, q => rfl
  | No r,  p, q => Void.exfalso (r p)

theorem Bool.symThenSelf [x y: Bool] (q: x = y): rfl = Eq.trans (Eq.sym q) q := J (y' q' => rfl = Eq.trans (Eq.sym q') q') rfl q

theorem Bool.fromCanon (x: Bool) (y: Bool) (p: x = y):
  p = Eq.trans (Eq.sym (Bool.canon (Bool.decEq x x) rfl)) (Bool.canon (Bool.decEq x y) p) :=
  J (y' p' => p' = Eq.trans (Eq.sym (Bool.canon (Bool.decEq x x) rfl)) (Bool.canon (Bool.decEq x y') p'))
    (Bool.symThenSelf (Bool.canon (Bool.decEq x x) rfl)) p

theorem Bool.uniqueEq (x : Bool) (y : Bool) (p : x = y) (q : x = y) : p = q :=
  J (z e => p = z)
    (J (r e => p = Eq.trans (Eq.sym (Bool.canon (Bool.decEq x x) rfl)) r)
      (Bool.fromCanon x y p) (Bool.canonConst (Bool.decEq x y) p q))
    (J (z e => z = q) rfl (Bool.fromCanon x y q))

