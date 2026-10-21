-- The Stitchwort prelude, loaded before every file.

-- The library's root is `Std` (docs/proposals/namespaces.md). What's declared
-- here without a namespace is visible in every program; the rest is written
-- with its namespace (`List.length`), or imported. The effect machinery is
-- used throughout what follows, so it's imported here.
import Effect (Comp, foldComp, bind, Plus, PlusRes, SigMap, sigInject,
  sigReply, translate, sigId, sigCompose, sigLeft, sigRight, swapOp,
  swapReply, sigSwap, NoOp, NoRes, Sig, sigOp, sigRes, caseInject, caseReply,
  sigCase, noInject, noReply, sigFromNo, handlePlus, runPure, Rec, RecRes,
  Delay, now, lift, bindD, mapSig, pfix)

-- Logic

-- The proposition with no proofs: false.
type Void: Prop

-- The proposition with exactly one proof: true.
type Unit: Prop =
  | Trivial

def Not (p: Prop): Prop := p -> Void

-- Both propositions hold.
type And (p: Prop) (q: Prop): Prop =
  | Both (left: p) (right: q)

-- At least one of the propositions holds: `p || q`.
type Or (p: Prop) (q: Prop): Prop =
  | Inl (left: p)
  | Inr (right: q)

theorem And.left: [p q: Prop] -> And p q -> p
  | Both a b => a

theorem And.right: [p q: Prop] -> And p q -> q
  | Both a b => b

theorem Or.neither: [p q: Prop] -> Not p -> Not q -> Not (Or p q)
  | r, s, Inl a => r a
  | r, s, Inr b => s b

-- From a proof of `Void`, anything follows. `()` means "there's no value to
-- match here", so no right-hand side is needed.
def Void.absurd: Void -> a
  | ()

-- The same for proofs. (Without universe polymorphism, `Void.absurd`'s `a` can
-- only be a type of data.)
def Void.exfalso: [p: Prop] -> Void -> p
  | ()

-- Numbers

-- Numbers are stored compactly, but mean exactly this. `Nat.add`, `Nat.sub`, `Nat.mul`,
-- `Nat.leq`, `Nat.equal`, `Nat.divFuel`, `Nat.decEq`, `Nat.equalRefl` and `Nat.equalSound` also
-- have native implementations, used when all their arguments are numbers.
-- Each computes exactly what the definition here computes, proofs included;
-- they're tested against these definitions.
type Nat: Type =
  | Zero
  | Succ (n: Nat)

-- `a + b` means `Nat.add a b`. It recurses on its first argument, so
-- `Succ m + n` computes to `Succ (m + n)`.
def Nat.add: Nat -> Nat -> Nat
  | Zero,   n => n
  | Succ m, n => Succ (Nat.add m n)

-- `a - b`, stopping at zero: `3 - 5 = 0`.
def Nat.sub: Nat -> Nat -> Nat
  | m,      Zero   => m
  | Zero,   Succ n => Zero
  | Succ m, Succ n => Nat.sub m n

-- `a * b`
def Nat.mul: Nat -> Nat -> Nat
  | Zero,   n => 0
  | Succ m, n => n + Nat.mul m n

def Nat.pred: Nat -> Nat
  | Zero   => Zero
  | Succ n => n

-- Booleans

type Bool: Type =
  | False
  | True

def Bool.not: Bool -> Bool
  | False => True
  | True  => False

-- `if c then a else b`. The branches take a (unused) proof of `Unit` so that
-- only the chosen one is evaluated.
def Bool.ifThenElse: [a: Type] -> Bool -> (Unit -> a) -> (Unit -> a) -> a
  | True,  t, e => t Trivial
  | False, t, e => e Trivial

-- `m <= n` and `m < n` are propositions, defined by computation.
def Nat.leq: Nat -> Nat -> Bool
  | Zero,   n      => True
  | Succ m, Zero   => False
  | Succ m, Succ n => Nat.leq m n

def Nat.LessEq (m: Nat) (n: Nat): Prop := Nat.leq m n = True

def Nat.LessThan (m: Nat) (n: Nat): Prop := Nat.leq (Succ m) n = True

-- Lists

type List (a: Type): Type =
  | Nil
  | Cons (head: a) (tail: List a)

-- `a` is bound automatically, as an implicit argument: `List.length: [a: Type] -> ...`.
def List.length: List a -> Nat
  | Nil       => 0
  | Cons x xs => Succ (List.length xs)

def List.append: List a -> List a -> List a
  | Nil,       ys => ys
  | Cons x xs, ys => Cons x (List.append xs ys)

-- A value that may be missing.
type Maybe (a: Type): Type =
  | Nothing
  | Just (value: a)

-- Two values together.
type Pair (a: Type) (b: Type): Type =
  | MkPair (fst: a) (snd: b)

def Pair.fst: Pair a b -> a
  | MkPair x y => x

def Pair.snd: Pair a b -> b
  | MkPair x y => y

-- `List.reverseOnto xs acc` is `xs` reversed, followed by `acc`.
def List.reverseOnto: List a -> List a -> List a
  | Nil,       acc => acc
  | Cons x xs, acc => List.reverseOnto xs (Cons x acc)

-- Equality lemmas, all built from `J`.

theorem Eq.cong (f: a -> b) [x y: a] (p: x = y): f x = f y := J (y' p' => f x = f y') rfl p

theorem Eq.sym [x y : a] (p : x = y) : y = x := J (y' p' => y' = x) rfl p

theorem Eq.trans [x y z: a] (p: x = y) (q: y = z): x = z := J (z' q' => x = z') p q

-- Different constructors are different. Each proof transports along the
-- equation into a family that's `Unit` at one constructor and `Void` at the other.

def Nat.IsZero: Nat -> Prop
  | Zero   => Unit
  | Succ n => Void

theorem Nat.zeroNotSucc (n: Nat): Not (0 = Succ n)
  | p => J (y q => Nat.IsZero y) Trivial p

theorem Nat.succNotZero (n: Nat): Not (Succ n = 0)
  | p => Nat.zeroNotSucc n (Eq.sym p)

theorem Nat.succInjective (m: Nat) (n: Nat) (p: Succ m = Succ n): m = n := Eq.cong Nat.pred p

def Bool.IsFalse: Bool -> Prop
  | False => Unit
  | True  => Void

theorem Bool.falseNotTrue: Not (False = True)
  | p => J (y q => Bool.IsFalse y) Trivial p

-- Whether two numbers are equal, as a `Bool`.
def Nat.equal: Nat -> Nat -> Bool
  | Zero,   Zero   => True
  | Zero,   Succ n => False
  | Succ m, Zero   => False
  | Succ m, Succ n => Nat.equal m n

theorem Nat.equalRefl: (n: Nat) -> Nat.equal n n = True
  | Zero   => rfl
  | Succ n => Nat.equalRefl n

-- Numbers that `Nat.equal` says are equal are equal.
theorem Nat.equalSound: (m: Nat) -> (n: Nat) -> Nat.equal m n = True -> m = n
  | Zero,   Zero,   h => rfl
  | Zero,   Succ n, h => Void.exfalso (Bool.falseNotTrue h)
  | Succ m, Zero,   h => Void.exfalso (Bool.falseNotTrue h)
  | Succ m, Succ n, h => Eq.cong Succ (Nat.equalSound m n h)

-- Numbers that `Nat.equal` says differ are different.
theorem Nat.equalFalse (m: Nat) (n: Nat) (h: Nat.equal m n = False): Not (m = n)
  | p => Bool.falseNotTrue (Eq.trans (Eq.sym h) (J (y q => Nat.equal m y = True) (Nat.equalRefl m) p))

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

theorem Bool.decTrueToBool : (c : Bool) -> Decidable.toBool (Bool.decTrue c) = c
  | True  => rfl
  | False => rfl

-- What `a == b` (a decision turned into a `Bool`) says about `a = b`, both ways.
theorem Decidable.toBoolSound: [p: Prop] -> (d: Decidable p) -> Decidable.toBool d = True -> p
  | Yes h, e => h
  | No r,  e => Void.exfalso (Bool.falseNotTrue e)

theorem Decidable.toBoolFalse: [p: Prop] -> (d: Decidable p) -> Decidable.toBool d = False -> Not p
  | Yes h, e, x => Void.exfalso (Bool.trueNotFalse e)
  | No r,  e, x => r x

theorem Decidable.toBoolOf: [p: Prop] -> (d: Decidable p) -> p -> Decidable.toBool d = True
  | Yes h, x => rfl
  | No r,  x => Void.exfalso (r x)

theorem Decidable.toBoolOfNot: [p: Prop] -> (d: Decidable p) -> Not p -> Decidable.toBool d = False
  | Yes h, n => Void.exfalso (n h)
  | No r,  n => rfl

-- Characters

-- Whether a number is a Unicode scalar value: at most 0x10FFFF, and not a
-- surrogate (0xD800 to 0xDFFF).
def Char.isScalar (n : Nat) : Bool := if Nat.leq 55296 n then (if Nat.leq n 57343 then False else Nat.leq n 1114111) else True

-- A Unicode scalar value. `'a'` is a `Char`; the compiler proves `valid` for
-- a literal by computation, and the kernel checks it.
type Char : Type =
  | MkChar (code : Nat) (valid : Char.isScalar code = True)

def Char.toNat : Char -> Nat
  | MkChar n v => n

def Char.fromNat (n : Nat) : Maybe Char := if h : Char.isScalar n = True then Just (MkChar n h) else Nothing

-- Characters with the same code are equal: their proofs of `valid` are too.
theorem Char.mkExt (a : Nat) (b : Nat) (p : Char.isScalar a = True) (e : a = b) :
  (q : Char.isScalar b = True) -> MkChar a p = MkChar b q :=
  J (b' e' => (q': Char.isScalar b' = True) -> MkChar a p = MkChar b' q')
    (q' => J (r e'' => MkChar a p = MkChar a r) rfl (Bool.uniqueEq (Char.isScalar a) True p q'))
    e

theorem Char.ext : (x : Char) -> (y : Char) -> Char.toNat x = Char.toNat y -> x = y
  | MkChar a p, MkChar b q, e => Char.mkExt a b p e q

def Char.decEqFrom (x : Char) (y : Char) : Decidable (Char.toNat x = Char.toNat y) -> Decidable (x = y)
  | Yes e => Yes (Char.ext x y e)
  | No r  => No (p => r (Eq.cong Char.toNat p))

def Char.decEq (x : Char) (y : Char) : Decidable (x = y) := Char.decEqFrom x y (Nat.decEq (Char.toNat x) (Char.toNat y))

-- Division

-- Counts how many times `d` fits into `n`, using `fuel` to stay structurally
-- recursive (`n` is always enough fuel when `d` isn't zero).
def Nat.divFuel: Nat -> Nat -> Nat -> Nat
  | Zero,      n, d => 0
  | Succ fuel, n, d => if Nat.leq d n then Succ (Nat.divFuel fuel (n - d) d) else 0

-- `n / d` and `n % d` need a proof that `d` isn't zero, which `auto` finds.
def Nat.div (n: Nat) (d: Nat): [auto ok: d != 0] -> Nat := Nat.divFuel n n d

-- The quotient goes on the left: `*` recurses on its left argument, so
-- `(n / d) * 100` stays put while checking, where `100 * (n / d)` would
-- unfold into a hundred additions.
def Nat.mod (n: Nat) (d: Nat): [auto ok: d != 0] -> Nat := n - (n / d) * d

theorem Nat.leSucc: (n: Nat) -> n <= Succ n
  | Zero => rfl
  | Succ n => Nat.leSucc n

theorem Nat.leTrans: (a: Nat) -> (b: Nat) -> (c: Nat) -> a <= b -> b <= c -> a <= c
  | Zero, b, c, h1, h2 => rfl
  | Succ a, Zero, c, h1, h2 => Void.exfalso (Bool.falseNotTrue h1)
  | Succ a, Succ b, Zero, h1, h2 => Void.exfalso (Bool.falseNotTrue h2)
  | Succ a, Succ b, Succ c, h1, h2 => Nat.leTrans a b c h1 h2

theorem Nat.lessLe (m: Nat) (n: Nat) (h: m < n): m <= n := Nat.leTrans m (Succ m) n (Nat.leSucc m) h

theorem Nat.lessTrans (m: Nat) (n: Nat) (p: Nat) (h1: m < n) (h2: n < p): m < p := Nat.leTrans (Succ m) n p h1 (Nat.lessLe n p h2)

-- Lists, continued

def List.IsNil: List a -> Prop
  | Nil       => Unit
  | Cons x xs => Void

theorem List.nilNotCons (x: a) (xs: List a): Not (Nil = Cons x xs)
  | p => J (y q => List.IsNil y) Trivial p

theorem List.consNotNil (x: a) (xs: List a): Not (Cons x xs = Nil)
  | p => List.nilNotCons x xs (Eq.sym p)

def List.headOr (d: a): List a -> a
  | Nil       => d
  | Cons x xs => x

def List.tailOf: List a -> List a
  | Nil       => Nil
  | Cons x xs => xs

def List.decCons (x: a) (y: a) (xs: List a) (ys: List a):
    Decidable (x = y) -> Decidable (xs = ys) -> Decidable (Cons x xs = Cons y ys)
  | Yes p, Yes q => Yes (J (y' p' => Cons x xs = Cons y' ys) (Eq.cong (Cons x) q) p)
  | No r,  dq    => No (e => r (Eq.cong (List.headOr x) e))
  | Yes p, No r  => No (e => r (Eq.cong List.tailOf e))

-- Equality of lists, from equality of their elements.
def List.decEq (d : (x : a) -> (y : a) -> Decidable (x = y)) : (xs : List a) -> (ys : List a) -> Decidable (xs = ys)
  | Nil,       Nil       => Yes rfl
  | Nil,       Cons y ys => No (List.nilNotCons y ys)
  | Cons x xs, Nil       => No (List.consNotNil x xs)
  | Cons x xs, Cons y ys => List.decCons x y xs ys (d x y) (List.decEq d xs ys)

def Pair.decMk (x1 : a) (x2 : a) (y1 : b) (y2 : b) :
    Decidable (x1 = x2) -> Decidable (y1 = y2) -> Decidable (MkPair x1 y1 = MkPair x2 y2)
  | Yes p, Yes q => Yes (J (x' p' => MkPair x1 y1 = MkPair x' y2) (Eq.cong (MkPair x1) q) p)
  | No r,  dq    => No (e => r (Eq.cong Pair.fst e))
  | Yes p, No r  => No (e => r (Eq.cong Pair.snd e))

-- Equality of pairs, from equality of their parts.
def Pair.decEq (da: (x: a) -> (y: a) -> Decidable (x = y)) (db: (x: b) -> (y: b) -> Decidable (x = y)):
    (p: Pair a b) -> (q: Pair a b) -> Decidable (p = q)
  | MkPair x1 y1, MkPair x2 y2 => Pair.decMk x1 x2 y1 y2 (da x1 x2) (db y1 y2)

def Maybe.IsNothing: Maybe a -> Prop
  | Nothing => Unit
  | Just x  => Void

theorem Maybe.nothingNotJust (x: a): Not (Nothing = Just x)
  | p => J (y q => Maybe.IsNothing y) Trivial p

theorem Maybe.justNotNothing (x: a): Not (Just x = Nothing)
  | p => Maybe.nothingNotJust x (Eq.sym p)

-- The value, or `d` if there isn't one.
def Maybe.withDefault (d: a): Maybe a -> a
  | Nothing => d
  | Just x  => x

def Maybe.decJust (x: a) (y: a): Decidable (x = y) -> Decidable (Just x = Just y)
  | Yes p => Yes (Eq.cong Just p)
  | No r  => No (e => r (Eq.cong (Maybe.withDefault x) e))

-- Equality of optional values, from equality of the values.
def Maybe.decEq (d: (x: a) -> (y: a) -> Decidable (x = y)): (m: Maybe a) -> (n: Maybe a) -> Decidable (m = n)
  | Nothing, Nothing => Yes rfl
  | Nothing, Just y  => No (Maybe.nothingNotJust y)
  | Just x,  Nothing => No (Maybe.justNotNothing x)
  | Just x,  Just y  => Maybe.decJust x y (d x y)

-- Comparisons

type Ordering: Type =
  | Less
  | Equal
  | Greater

def Nat.compare (m: Nat) (n: Nat): Ordering := if Nat.equal m n then Equal else (if Nat.leq m n then Less else Greater)

-- The first comparison, unless it's `Equal`.
def Ordering.andThen: Ordering -> Ordering -> Ordering
  | Less,    o => Less
  | Equal,   o => o
  | Greater, o => Greater

def Ordering.index: Ordering -> Nat
  | Less    => 0
  | Equal   => 1
  | Greater => 2

def Ordering.decEq: (a: Ordering) -> (b: Ordering) -> Decidable (a = b)
  | Less,    Less    => Yes rfl
  | Less,    Equal   => No (p => Nat.zeroNotSucc 0 (Eq.cong Ordering.index p))
  | Less,    Greater => No (p => Nat.zeroNotSucc 1 (Eq.cong Ordering.index p))
  | Equal,   Less    => No (p => Nat.zeroNotSucc 0 (Eq.sym (Eq.cong Ordering.index p)))
  | Equal,   Equal   => Yes rfl
  | Equal,   Greater => No (p => Nat.zeroNotSucc 0 (Nat.succInjective 0 1 (Eq.cong Ordering.index p)))
  | Greater, Less    => No (p => Nat.zeroNotSucc 1 (Eq.sym (Eq.cong Ordering.index p)))
  | Greater, Equal   => No (p => Nat.zeroNotSucc 0 (Nat.succInjective 0 1 (Eq.sym (Eq.cong Ordering.index p))))
  | Greater, Greater => Yes rfl

def List.concatMap (f: a -> List b): List a -> List b
  | Nil       => Nil
  | Cons x xs => List.append (f x) (List.concatMap f xs)

-- Lemmas the rest of the prelude uses. (Sorting and the lemmas around it are
-- the library file std/List/Sort.sw; these stay because the core, or a
-- later section that hasn't moved, needs them.)

-- `Bool.inspect b motive t f` proves `motive b` by cases on `b`, remembering
-- which case it is. A proof about `if le x y then ... else ...` uses it with
-- `b = le x y` to get the branch's evidence (`le x y = True` or `= False`).
theorem Bool.inspect: (b: Bool) -> (motive: Bool -> Prop) -> (b = True -> motive True) -> (b = False -> motive False) -> motive b
  | True,  m, t, f => t rfl
  | False, m, t, f => f rfl

-- 1 for `True`, 0 for `False`.
def Bool.toNat: Bool -> Nat
  | False => 0
  | True  => 1

-- Text (docs/proposals/text-and-io.md)

-- A sequence of Unicode scalar values. `"héllo"` is a `Text`. Equality and
-- ordering compare the sequence exactly, by scalar value, and length counts
-- scalar values; nothing is normalised, so `"\u{E9}"` and `"e\u{301}"` are
-- different texts. Code that goes through `Text.toList` and `Text.fromList`
-- and their lemmas, rather than `MkText`, won't depend on the representation.
type Text: Type =
  | MkText (chars: List Char)

def Text.toList: Text -> List Char
  | MkText cs => cs

def Text.fromList (cs: List Char): Text := MkText cs

theorem Text.fromToList: (t: Text) -> Text.fromList (Text.toList t) = t
  | MkText cs => rfl

-- `a ++ b`
def Text.append (a: Text) (b: Text): Text := MkText (List.append (Text.toList a) (Text.toList b))

-- The number of scalar values.
def Text.length (t: Text): Nat := List.length (Text.toList t)

def Text.isEmpty: Text -> Bool
  | MkText Nil         => True
  | MkText (Cons c cs) => False

def Text.decEqFrom (a: Text) (b: Text): Decidable (Text.toList a = Text.toList b) -> Decidable (a = b)
  | Yes p => Yes (Eq.trans (Eq.sym (Text.fromToList a)) (Eq.trans (Eq.cong Text.fromList p) (Text.fromToList b)))
  | No r  => No (p => r (Eq.cong Text.toList p))

def Text.decEq (a: Text) (b: Text): Decidable (a = b) := Text.decEqFrom a b (List.decEq Char.decEq (Text.toList a) (Text.toList b))

-- The first character and the rest, unless the text is empty.
def Text.uncons: Text -> Maybe (Pair Char Text)
  | MkText Nil         => Nothing
  | MkText (Cons c cs) => Just (MkPair c (MkText cs))

def Text.foldChars (f: Char -> b -> b) (z: b): List Char -> b
  | Nil       => z
  | Cons c cs => f c (Text.foldChars f z cs)

-- `Text.fold f z "abc"` is `f 'a' (f 'b' (f 'c' z))`.
def Text.fold (f: Char -> b -> b) (z: b) (t: Text): b := Text.foldChars f z (Text.toList t)

def Text.compareChars: List Char -> List Char -> Ordering
  | Nil,       Nil       => Equal
  | Nil,       Cons y ys => Less
  | Cons x xs, Nil       => Greater
  | Cons x xs, Cons y ys =>
    Ordering.andThen (Nat.compare (Char.toNat x) (Char.toNat y)) (Text.compareChars xs ys)

-- Lexicographic, by scalar value. (Not JavaScript's order, which compares
-- UTF-16 code units: there, "\u{10000}" sorts before "\u{E000}".)
def Text.compare (a: Text) (b: Text): Ordering := Text.compareChars (Text.toList a) (Text.toList b)

-- Whitespace, for `Text.trim`: exactly space, tab, line feed, vertical tab,
-- form feed and carriage return. Not Unicode's `White_Space`.
def Char.isSpaceCode: Nat -> Bool
  | 9  => True
  | 10 => True
  | 11 => True
  | 12 => True
  | 13 => True
  | 32 => True
  | _  => False

def Char.isSpace (c: Char): Bool := Char.isSpaceCode (Char.toNat c)

def Text.dropSpaces: List Char -> List Char
  | Nil       => Nil
  | Cons c cs => if Char.isSpace c then Text.dropSpaces cs else Cons c cs

-- Removes whitespace (as `Char.isSpace` defines it) from both ends.
def Text.trim (t: Text): Text := MkText (List.reverseOnto (Text.dropSpaces (List.reverseOnto (Text.dropSpaces (Text.toList t)) Nil)) Nil)

-- Numbers as text

def Nat.digitChar: Nat -> Char
  | 0 => '0'
  | 1 => '1'
  | 2 => '2'
  | 3 => '3'
  | 4 => '4'
  | 5 => '5'
  | 6 => '6'
  | 7 => '7'
  | 8 => '8'
  | _ => '9'

-- The digits of `n` in front of `acc`. `fuel` keeps it structurally
-- recursive; `n + 1` is always enough.
def Nat.digitsOnto: Nat -> Nat -> List Char -> List Char
  | Zero,      n, acc => acc
  | Succ fuel, n, acc =>
    if Nat.leq n 9 then Cons (Nat.digitChar n) acc else Nat.digitsOnto fuel (n / 10) (Cons (Nat.digitChar (n % 10)) acc)

-- Decimal, without leading zeros: `Nat.toText 42` is `"42"`.
def Nat.toText (n: Nat): Text := MkText (Nat.digitsOnto (Succ n) n Nil)

def Maybe.andThen (f: a -> Maybe b): Maybe a -> Maybe b
  | Nothing => Nothing
  | Just x  => f x

def Maybe.map (f: a -> b): Maybe a -> Maybe b
  | Nothing => Nothing
  | Just x  => Just (f x)

def Char.digitValue (c: Char): Maybe Nat := if Nat.leq 48 (Char.toNat c) then (if Nat.leq (Char.toNat c) 57 then Just (Char.toNat c - 48) else Nothing) else Nothing

def Text.readDigits (acc: Nat): List Char -> Maybe Nat
  | Nil       => Just acc
  | Cons c cs => Maybe.andThen (d => Text.readDigits (acc * 10 + d) cs) (Char.digitValue c)

-- A non-empty sequence of ASCII digits, and nothing else: no sign,
-- whitespace or separators. Leading zeros are allowed, so
-- `Text.toNat (Nat.toText n) = Just n` but `"007"` reads as 7.
def Text.toNat: Text -> Maybe Nat
  | MkText Nil         => Nothing
  | MkText (Cons c cs) => Text.readDigits 0 (Cons c cs)

-- Integers (docs/proposals/integers.md)

-- An integer: `OfNat n` is `n`, and `NegSucc n` is `-(n + 1)`, so each
-- integer has exactly one form. The definitions compute through `Nat`'s, so
-- they're as compact as `Nat` is, and the kernel needs nothing new.
type Int: Type =
  | OfNat (n: Nat)
  | NegSucc (n: Nat)

def Nat.toInt (n: Nat): Int := OfNat n

-- `-x`
def Int.neg: Int -> Int
  | OfNat Zero     => OfNat Zero
  | OfNat (Succ n) => NegSucc n
  | NegSucc n      => OfNat (Succ n)

-- `m - n` for naturals, as an integer. One subtraction decides which side
-- is bigger: `n - m` is zero exactly when `n <= m`.
def Int.subNatNatFrom (m: Nat) (n: Nat): Nat -> Int
  | Zero   => OfNat (m - n)
  | Succ k => NegSucc k

def Int.subNatNat (m: Nat) (n: Nat): Int := Int.subNatNatFrom m n (n - m)

-- `a + b`
def Int.add: Int -> Int -> Int
  | OfNat m,   OfNat n   => OfNat (m + n)
  | OfNat m,   NegSucc n => Int.subNatNat m (Succ n)
  | NegSucc m, OfNat n   => Int.subNatNat n (Succ m)
  | NegSucc m, NegSucc n => NegSucc (Succ (m + n))

-- `a - b`
def Int.sub (a: Int) (b: Int): Int := Int.add a (Int.neg b)

-- `a * b`. By constructors first, so `OfNat m * OfNat n` is `OfNat (m * n)`.
def Int.mul: Int -> Int -> Int
  | OfNat m,   OfNat n   => OfNat (m * n)
  | OfNat m,   NegSucc n => Int.neg (OfNat (m * Succ n))
  | NegSucc m, OfNat n   => Int.neg (OfNat (Succ m * n))
  | NegSucc m, NegSucc n => OfNat (Succ m * Succ n)

-- `|x|`, as a `Nat`.
def Int.natAbs: Int -> Nat
  | OfNat n   => n
  | NegSucc n => Succ n

-- `x` if it isn't negative, otherwise `0`.
def Int.toNat: Int -> Nat
  | OfNat n   => n
  | NegSucc n => 0

-- The two constructors are different, and each is injective.

def Int.IsOfNat: Int -> Prop
  | OfNat n   => Unit
  | NegSucc n => Void

theorem Int.ofNatNotNegSucc (m: Nat) (n: Nat): Not (OfNat m = NegSucc n)
  | p => J (y q => Int.IsOfNat y) Trivial p

theorem Int.negSuccNotOfNat (m: Nat) (n: Nat): Not (NegSucc m = OfNat n)
  | p => Int.ofNatNotNegSucc n m (Eq.sym p)

theorem Int.ofNatInjective (m: Nat) (n: Nat) (p: OfNat m = OfNat n): m = n := Eq.cong Int.toNat p

theorem Int.negSuccInjective (m: Nat) (n: Nat) (p: NegSucc m = NegSucc n): m = n := Nat.succInjective m n (Eq.cong Int.natAbs p)

def Int.decOfNat (m: Nat) (n: Nat): Decidable (m = n) -> Decidable (OfNat m = OfNat n)
  | Yes p => Yes (Eq.cong OfNat p)
  | No r  => No (p => r (Int.ofNatInjective m n p))

def Int.decNegSucc (m: Nat) (n: Nat): Decidable (m = n) -> Decidable (NegSucc m = NegSucc n)
  | Yes p => Yes (Eq.cong NegSucc p)
  | No r  => No (p => r (Int.negSuccInjective m n p))

-- For two integers this computes `Yes rfl` or a `No` of constant size,
-- however big they are, since `Nat.decEq` does.
def Int.decEq: (a: Int) -> (b: Int) -> Decidable (a = b)
  | OfNat m,   OfNat n   => Int.decOfNat m n (Nat.decEq m n)
  | OfNat m,   NegSucc n => No (Int.ofNatNotNegSucc m n)
  | NegSucc m, OfNat n   => No (Int.negSuccNotOfNat m n)
  | NegSucc m, NegSucc n => Int.decNegSucc m n (Nat.decEq m n)

-- `a <= b`. Every negative is below every non-negative; among negatives the
-- order flips, since `NegSucc n` is `-(n+1)`.
def Int.leq: Int -> Int -> Bool
  | OfNat m,   OfNat n   => Nat.leq m n
  | OfNat m,   NegSucc n => False
  | NegSucc m, OfNat n   => True
  | NegSucc m, NegSucc n => Nat.leq n m

-- `a < b`
def Int.less: Int -> Int -> Bool
  | OfNat m,   OfNat n   => Nat.leq (Succ m) n
  | OfNat m,   NegSucc n => False
  | NegSucc m, OfNat n   => True
  | NegSucc m, NegSucc n => Nat.leq (Succ n) m

def Int.LessEq (a: Int) (b: Int): Prop := Int.leq a b = True

def Int.LessThan (a: Int) (b: Int): Prop := Int.less a b = True

instance Int.decLessEq (a: Int) (b: Int): Decidable (Int.LessEq a b) := Bool.decTrue (Int.leq a b)

instance Int.decLessThan (a: Int) (b: Int): Decidable (Int.LessThan a b) := Bool.decTrue (Int.less a b)

def Int.compare: Int -> Int -> Ordering
  | OfNat m,   OfNat n   => Nat.compare m n
  | OfNat m,   NegSucc n => Greater
  | NegSucc m, OfNat n   => Less
  | NegSucc m, NegSucc n => Nat.compare n m

-- `|x|`, as an `Int`.
def Int.abs: Int -> Int
  | OfNat n   => OfNat n
  | NegSucc n => OfNat (Succ n)

-- `Just x` if `x` isn't negative, otherwise `Nothing`.
def Int.toNatChecked: Int -> Maybe Nat
  | OfNat n   => Just n
  | NegSucc n => Nothing

-- `-1`, `0` or `1`.
def Int.sign: Int -> Int
  | OfNat Zero     => OfNat Zero
  | OfNat (Succ n) => OfNat 1
  | NegSucc n      => NegSucc 0

-- Decimal, with a `-` in front of a negative: `"-42"`. Never `"-0"`.
def Int.toText: Int -> Text
  | OfNat n   => Nat.toText n
  | NegSucc n => MkText (Cons '-' (Text.toList (Nat.toText (Succ n))))

-- An optional `-`, then one or more ASCII digits, and nothing else. Leading
-- zeros are fine and `"-0"` is `0`; `"-"`, `""` and `"+5"` are `Nothing`.
def Text.toInt: Text -> Maybe Int
  | MkText Nil         => Nothing
  | MkText (Cons c cs) =>
    if Nat.equal (Char.toNat c) 45
    then Maybe.map (n => Int.neg (OfNat n)) (Text.toNat (MkText cs))
    else Maybe.map OfNat (Text.toNat (MkText (Cons c cs)))

-- Division. `a / d` and `a % d` are Euclidean: `a = d * (a / d) + a % d`
-- with `0 <= a % d < |d|`, whatever the signs, so `-18 % 100` is `82`.
-- Each case divides naturals by a `Succ n`, which `auto` sees isn't zero.
-- The divisor can't be zero, but the case still has to be covered: `ok`
-- rules it out.
def Int.div: (a: Int) -> (d: Int) -> [auto ok: d != OfNat 0] -> Int
  | a,         OfNat Zero     => Void.absurd (ok rfl)
  | OfNat m,   OfNat (Succ n) => OfNat (m / Succ n)
  | NegSucc m, OfNat (Succ n) => NegSucc (m / Succ n)
  | OfNat m,   NegSucc n      => Int.neg (OfNat (m / Succ n))
  | NegSucc m, NegSucc n      => OfNat (Succ (m / Succ n))

-- Never negative. For `NegSucc m`, `m % Succ n <= n`, so the subtraction
-- doesn't stop at zero.
def Int.mod: (a: Int) -> (d: Int) -> [auto ok: d != OfNat 0] -> Int
  | a,         OfNat Zero     => Void.absurd (ok rfl)
  | OfNat m,   OfNat (Succ n) => OfNat (m % Succ n)
  | NegSucc m, OfNat (Succ n) => OfNat (n - m % Succ n)
  | OfNat m,   NegSucc n      => OfNat (m % Succ n)
  | NegSucc m, NegSucc n      => OfNat (n - m % Succ n)

-- `x % d` as a `Nat`, for indexing: `(x.modNat d).toInt = x % d.toInt`.
def Int.modNat: Int -> (d: Nat) -> [auto ok: d != 0] -> Nat
  | x,         Zero   => Void.absurd (ok rfl)
  | OfNat m,   Succ n => m % Succ n
  | NegSucc m, Succ n => n - m % Succ n

-- Truncating division, rounding toward zero; the remainder has the
-- dividend's sign (C, Rust's `/` and `%`, JavaScript's `BigInt`).
def Int.tdiv: (a: Int) -> (d: Int) -> [auto ok: d != OfNat 0] -> Int
  | a,         OfNat Zero     => Void.absurd (ok rfl)
  | OfNat m,   OfNat (Succ n) => OfNat (m / Succ n)
  | NegSucc m, OfNat (Succ n) => Int.neg (OfNat (Succ m / Succ n))
  | OfNat m,   NegSucc n      => Int.neg (OfNat (m / Succ n))
  | NegSucc m, NegSucc n      => OfNat (Succ m / Succ n)

def Int.tmod: (a: Int) -> (d: Int) -> [auto ok: d != OfNat 0] -> Int
  | a,         OfNat Zero     => Void.absurd (ok rfl)
  | OfNat m,   OfNat (Succ n) => OfNat (m % Succ n)
  | NegSucc m, OfNat (Succ n) => Int.neg (OfNat (Succ m % Succ n))
  | OfNat m,   NegSucc n      => OfNat (m % Succ n)
  | NegSucc m, NegSucc n      => Int.neg (OfNat (Succ m % Succ n))

-- Flooring division, rounding toward negative infinity; the remainder has
-- the divisor's sign (Python, Haskell's `div` and `mod`). The same as
-- Euclidean division when the divisor is positive.
def Int.fdiv: (a: Int) -> (d: Int) -> [auto ok: d != OfNat 0] -> Int
  | a,              OfNat Zero     => Void.absurd (ok rfl)
  | OfNat m,        OfNat (Succ n) => OfNat (m / Succ n)
  | NegSucc m,      OfNat (Succ n) => NegSucc (m / Succ n)
  | OfNat Zero,     NegSucc n      => OfNat Zero
  | OfNat (Succ m), NegSucc n      => NegSucc (m / Succ n)
  | NegSucc m,      NegSucc n      => OfNat (Succ m / Succ n)

def Int.fmod: (a: Int) -> (d: Int) -> [auto ok: d != OfNat 0] -> Int
  | a,              OfNat Zero     => Void.absurd (ok rfl)
  | OfNat m,        OfNat (Succ n) => OfNat (m % Succ n)
  | NegSucc m,      OfNat (Succ n) => OfNat (n - m % Succ n)
  | OfNat Zero,     NegSucc n      => OfNat Zero
  | OfNat (Succ m), NegSucc n      => Int.neg (OfNat (n - m % Succ n))
  | NegSucc m,      NegSucc n      => Int.neg (OfNat (Succ m % Succ n))

-- Splitting and joining

-- `Text.splitChars s cs` is the first field and the rest: never empty.
def Text.splitCons (s: Char) (c: Char): Bool -> Pair (List Char) (List (List Char)) -> Pair (List Char) (List (List Char))
  | True,  MkPair f fs => MkPair Nil (Cons f fs)
  | False, MkPair f fs => MkPair (Cons c f) fs

def Text.splitChars (s: Char): List Char -> Pair (List Char) (List (List Char))
  | Nil       => MkPair Nil Nil
  | Cons c cs => Text.splitCons s c (Decidable.toBool (Char.decEq c s)) (Text.splitChars s cs)

def Text.joinChars (s: Char) (f: List Char): List (List Char) -> List Char
  | Nil       => f
  | Cons g gs => List.append f (Cons s (Text.joinChars s g gs))

def Text.textsOf: List (List Char) -> List Text
  | Nil       => Nil
  | Cons f fs => Cons (MkText f) (Text.textsOf fs)

def Text.charListsOf: List Text -> List (List Char)
  | Nil       => Nil
  | Cons t ts => Cons (Text.toList t) (Text.charListsOf ts)

def Text.splitTexts: Pair (List Char) (List (List Char)) -> List Text
  | MkPair f fs => Cons (MkText f) (Text.textsOf fs)

-- The fields between separators, keeping empty ones: splitting "a,,b" on
-- ',' gives ["a", "", "b"], and splitting "" gives [""].
def Text.split (s: Char) (t: Text): List Text := Text.splitTexts (Text.splitChars s (Text.toList t))

-- The texts with `s` between them. `Text.join s (Text.split s t) = t`.
def Text.join (s: Char): List Text -> Text
  | Nil       => MkText Nil
  | Cons t ts => MkText (Text.joinChars s (Text.toList t) (Text.charListsOf ts))

-- Computations (docs/proposals/abilities.md)

-- A computation that returns an `a`, performing operations from a signature:
-- `op` is the type of operation calls, and `res o` is what call `o` gives
-- back. Every computation is a finite tree, so folds over it terminate.
type Effect.Comp (op: Type) (res: op -> Type) (a: Type): Type =
  | Done (value: a)
  | Call (o: op) (rest: res o -> Comp op res a)

-- The fold over a computation. `call` gets each operation together with the
-- results of folding every way it could continue, and may use them any
-- number of times. A deep handler is a fold.
def Effect.foldComp [op: Type] [res: op -> Type] [a r: Type]
    (done: a -> r) (call: (o: op) -> (res o -> r) -> r): Comp op res a -> r
  | Done x      => done x
  | Call o rest => call o (y => foldComp done call (rest y))

-- Sequencing: run `c`, then `next` with its result.
def Effect.bind: [op: Type] -> [res: op -> Type] -> [a b: Type] ->
    Comp op res a -> (a -> Comp op res b) -> Comp op res b
  | Done x,      next => next x
  | Call o rest, next => Call o (y => bind (rest y) next)

-- Rows: signatures side by side, and mappings between signatures.

-- The operations of two signatures: the row `{l, r}`.
type Effect.Plus (l: Type) (r: Type): Type =
  | L (o: l)
  | R (o: r)

def Effect.PlusRes [l r: Type] (lres: l -> Type) (rres: r -> Type): Plus l r -> Type
  | L o => lres o
  | R o => rres o

-- A mapping from one signature into another. Because what an operation
-- returns depends on the operation, a mapping says both where each
-- operation goes and how its response comes back.
type Effect.SigMap (op1: Type) (res1: op1 -> Type) (op2: Type) (res2: op2 -> Type): Type =
  | MkSigMap (inject: op1 -> op2) (reply: (o: op1) -> res2 (inject o) -> res1 o)

def Effect.sigInject: [op1: Type] -> [res1: op1 -> Type] -> [op2: Type] -> [res2: op2 -> Type] ->
    SigMap op1 res1 op2 res2 -> op1 -> op2
  | MkSigMap inj rep, o => inj o

def Effect.sigReply: [op1: Type] -> [res1: op1 -> Type] -> [op2: Type] -> [res2: op2 -> Type] ->
    (m: SigMap op1 res1 op2 res2) -> (o: op1) -> res2 (sigInject m o) -> res1 o
  | MkSigMap inj rep, o, r => rep o r

-- Moves a computation along a mapping. Operations stay in the same order;
-- only their names in the signature change.
def Effect.translate [op1: Type] [res1: op1 -> Type] [op2: Type] [res2: op2 -> Type] [a: Type]
    (m: SigMap op1 res1 op2 res2): Comp op1 res1 a -> Comp op2 res2 a
  | Done x      => Done x
  | Call o rest => Call (sigInject m o) (r => translate m (rest (sigReply m o r)))

def Effect.sigId: [op: Type] -> [res: op -> Type] -> SigMap op res op res := MkSigMap (o => o) (o r => r)

def Effect.sigCompose: [op1: Type] -> [res1: op1 -> Type] -> [op2: Type] -> [res2: op2 -> Type] ->
    [op3: Type] -> [res3: op3 -> Type] ->
    SigMap op1 res1 op2 res2 -> SigMap op2 res2 op3 res3 -> SigMap op1 res1 op3 res3
  | MkSigMap i1 r1, MkSigMap i2 r2 =>
    MkSigMap (o => i2 (i1 o)) (o r => r1 o (r2 (i1 o) r))

-- Weakening: a signature into a row with something else on the right or left.
def Effect.sigLeft: [l r: Type] -> [lres: l -> Type] -> [rres: r -> Type] ->
  SigMap l lres (Plus l r) (PlusRes lres rres) := MkSigMap (o => L o) (o x => x)

def Effect.sigRight: [l r: Type] -> [lres: l -> Type] -> [rres: r -> Type] ->
  SigMap r rres (Plus l r) (PlusRes lres rres) := MkSigMap (o => R o) (o x => x)

-- Reordering: `{l, r}` to `{r, l}`.
def Effect.swapOp: [l r: Type] -> Plus l r -> Plus r l
  | L o => R o
  | R o => L o

def Effect.swapReply: [l r: Type] -> [lres: l -> Type] -> [rres: r -> Type] ->
    (o: Plus l r) -> PlusRes rres lres (swapOp o) -> PlusRes lres rres o
  | L o, x => x
  | R o, x => x

def Effect.sigSwap: [l r: Type] -> [lres: l -> Type] -> [rres: r -> Type] ->
  SigMap (Plus l r) (PlusRes lres rres) (Plus r l) (PlusRes rres lres) := MkSigMap swapOp swapReply

-- Support for abilities (docs/proposals/abilities.md). The elaborator
-- translates `ability`, rows `{A | e}`, effectful code and `handle` into these.

-- `()`: the unit type and its only value.
type Builtin.UnitType: Type =
  | UnitValue

-- The signature with no operations: the end of a closed row.
type Effect.NoOp: Type

def Effect.NoRes: NoOp -> Type
  | ()

-- A signature as one value, so a row variable `e` is one parameter.
type Effect.Sig: Type 1 =
  | MkSig (op: Type) (res: op -> Type)

def Effect.sigOp: Sig -> Type
  | MkSig op res => op

def Effect.sigRes: (s: Sig) -> sigOp s -> Type
  | MkSig op res, a1 => res a1

-- Combining two mappings into one from `{l, r}`.
def Effect.caseInject [l r t: Type] [lres: l -> Type] [rres: r -> Type] [tres: t -> Type]
    (ml: SigMap l lres t tres) (mr: SigMap r rres t tres): Plus l r -> t
  | L o => sigInject ml o
  | R o => sigInject mr o

def Effect.caseReply [l r t: Type] [lres: l -> Type] [rres: r -> Type] [tres: t -> Type]
    (ml: SigMap l lres t tres) (mr: SigMap r rres t tres):
    (o: Plus l r) -> tres (caseInject ml mr o) -> PlusRes lres rres o
  | L o, x => sigReply ml o x
  | R o, x => sigReply mr o x

def Effect.sigCase [l r t: Type] [lres: l -> Type] [rres: r -> Type] [tres: t -> Type]
  (ml: SigMap l lres t tres) (mr: SigMap r rres t tres): SigMap (Plus l r) (PlusRes lres rres) t tres := MkSigMap (caseInject ml mr) (caseReply ml mr)

-- The empty signature maps into anything.
def Effect.noInject: [t: Type] -> NoOp -> t
  | ()

def Effect.noReply: [t: Type] -> [tres: t -> Type] -> (o: NoOp) -> tres (noInject o) -> NoRes o
  | (), _

def Effect.sigFromNo: [t: Type] -> [tres: t -> Type] -> SigMap NoOp NoRes t tres := MkSigMap noInject noReply

-- A handler's step for the row `{l, r}`, from steps for each side.
def Effect.handlePlus [l r: Type] [lres: l -> Type] [rres: r -> Type] [res: Type]
    (fl: (o: l) -> (lres o -> res) -> res) (fr: (o: r) -> (rres o -> res) -> res):
    (o: Plus l r) -> (PlusRes lres rres o -> res) -> res
  | L o, k => fl o k
  | R o, k => fr o k

-- A computation that performs nothing is just its result.
def Effect.runPure: [a: Type] -> Comp NoOp NoRes a -> a
  | Done x => x
  | Call () rest

-- Partial computations (docs/proposals/partial.md)

-- A recursion request: run the definition being defined again on `x`. A
-- partial definition's body makes these instead of calling itself.
type Effect.Rec (req: Type): Type =
  | Recur (x: req)

-- What a request is answered with.
def Effect.RecRes [req: Type] (ans: req -> Type): Rec req -> Type
  | Recur x => ans x

-- A computation that may not finish: what `{Partial | e} a` stands for.
-- These have no definitions, and nothing can look inside a `Delay`: only
-- the runtime runs one, a step at a time. The kernel admits them as
-- primitives, after checking their types are exactly these.
def Effect.Delay: (op: Type) -> (res: op -> Type) -> Type -> Type

-- Finished, with this result.
def Effect.now: [op: Type] -> [res: op -> Type] -> [a: Type] -> a -> Delay op res a

-- A computation that finishes, as one that might not.
def Effect.lift: [op: Type] -> [res: op -> Type] -> [a: Type] -> Comp op res a -> Delay op res a

-- Sequencing.
def Effect.bindD: [op: Type] -> [res: op -> Type] -> [a b: Type] ->
  Delay op res a -> (a -> Delay op res b) -> Delay op res b

-- Moves a computation along a mapping between signatures.
def Effect.mapSig: [op1: Type] -> [res1: op1 -> Type] -> [op2: Type] -> [res2: op2 -> Type] -> [a: Type] ->
  SigMap op1 res1 op2 res2 -> Delay op1 res1 a -> Delay op2 res2 a

-- The recursive function a description defines: each `Recur y` its body
-- requests is answered by running the body on `y`.
def Effect.pfix: [op: Type] -> [res: op -> Type] -> [req: Type] -> [ans: req -> Type] ->
  ((x: req) -> Delay (Plus (Rec req) op) (PlusRes (RecRes ans) res) (ans x)) ->
  (x: req) -> Delay op res (ans x)

-- Input and output (docs/proposals/text-and-io.md, Part 2)

-- The console. Only a host interpreter performs these for real; in Stitchwort
-- code, `IO.simulate` interprets them as data.
ability IO where
  print: Text -> {IO} ()          -- writes the text, then a line ending
  readLine: () -> {IO} (Maybe Text)  -- Nothing only at end of input
  readAll: () -> {IO} Text          -- the rest of the input, all at once

-- The first line of scripted input, if there is one.
def IO.nextLine: List Text -> Maybe Text
  | Nil       => Nothing
  | Cons l ls => Just l

-- All of the scripted input, as `IO.readAll` gives it: each line followed by a
-- line feed, as a real interpreter would read it.
def IO.restOf (ins: List Text): Text :=
  MkText (List.concatMap (l => List.append (Text.toList l) ['\n']) ins)

-- Runs a program against scripted input lines: each `IO.readLine` takes the
-- next one, and gives `Nothing` once they're used up; `IO.readAll` takes all
-- that are left (see `IO.restOf`), after which `IO.readLine` gives `Nothing`
-- and `IO.readAll` gives "". Records each `IO.print` payload, in order, with the
-- result. A payload is one entry even if it contains a line feed: a real
-- interpreter writes each payload followed by a line ending. The payloads
-- are collected in reverse and turned round at the end, so a long run
-- doesn't build a deep chain of pending pairs.
def IO.simulate (input: List Text) (prog: () -> {IO | e} a): {e} Pair (List Text) a :=
  let run: List Text -> List Text -> {e} Pair (List Text) a :=
    handle prog() with
      | return x      => ins out => MkPair (List.reverseOnto out Nil) x
      | IO.print t, k    => ins out => k() ins (Cons t out)
      | IO.readLine u, k => ins out => k (IO.nextLine ins) (List.tailOf ins) out
      | IO.readAll u, k  => ins out => k (IO.restOf ins) Nil out
  run input Nil

-- Decidable equality (docs/proposals/interfaces.md §6.1): `a == b`,
-- `a != b`, `if h: a = b` and `auto` deciding an equation all use the
-- `DecEq` instance for the type. A data type or record declared in a
-- program gets one derived, when it can (`T.%instDecEq`).

interface DecEq (a: Type) =
  { decide: (x: a) -> (y: a) -> Decidable (x = y) }

instance Nat.instDecEq: DecEq Nat := { decide = Nat.decEq }

instance Int.instDecEq: DecEq Int := { decide = Int.decEq }

instance Bool.instDecEq: DecEq Bool := { decide = Bool.decEq }

instance Char.instDecEq: DecEq Char := { decide = Char.decEq }

instance Text.instDecEq: DecEq Text := { decide = Text.decEq }

instance Ordering.instDecEq: DecEq Ordering := { decide = Ordering.decEq }

instance List.instDecEq [auto decEq: DecEq a]: DecEq (List a) :=
  { decide = List.decEq (x y => DecEq.decide x y) }

instance Pair.instDecEq [auto decEqA: DecEq a] [auto decEqB: DecEq b]: DecEq (Pair a b) :=
  { decide = Pair.decEq (x y => DecEq.decide x y) (x y => DecEq.decide x y) }

instance Maybe.instDecEq [auto decEq: DecEq a]: DecEq (Maybe a) :=
  { decide = Maybe.decEq (x y => DecEq.decide x y) }

-- `x == y` says `x = y`.
theorem DecEq.sound [auto decEq: DecEq a] (x: a) (y: a) (h: (x == y) = True): x = y :=
  Decidable.toBoolSound (DecEq.decide x y) h

-- Proofs of an equation in a type with decidable equality are unique:
-- Hedberg's argument, as for `Bool` above. `DecEq.canon` turns any proof of
-- `x = y` into the one the decision gives, ignoring which proof it was
-- given, and every proof can be recovered from its canonical one.
def DecEq.canon: [x y: a] -> Decidable (x = y) -> x = y -> x = y
  | Yes e, p => e
  | No r,  p => Void.exfalso (r p)

theorem DecEq.canonConst: [x y: a] -> (d: Decidable (x = y)) -> (p: x = y) -> (q: x = y) ->
    DecEq.canon d p = DecEq.canon d q
  | Yes e, p, q => rfl
  | No r,  p, q => Void.exfalso (r p)

theorem DecEq.symThenSelf [x y: a] (q: x = y): rfl = Eq.trans (Eq.sym q) q := J (y' q' => rfl = Eq.trans (Eq.sym q') q') rfl q

theorem DecEq.fromCanon [auto decEq: DecEq a] (x: a) (y: a) (p: x = y):
  p = Eq.trans (Eq.sym (DecEq.canon (DecEq.decide [decEq := decEq] x x) rfl)) (DecEq.canon (DecEq.decide [decEq := decEq] x y) p) :=
  J (y' p' => p' = Eq.trans (Eq.sym (DecEq.canon (DecEq.decide [decEq := decEq] x x) rfl)) (DecEq.canon (DecEq.decide [decEq := decEq] x y') p'))
    (DecEq.symThenSelf (DecEq.canon (DecEq.decide [decEq := decEq] x x) rfl)) p

theorem DecEq.uniqueEq [auto decEq: DecEq a] [x y: a] (p: x = y) (q: x = y): p = q :=
  J (z e => p = z)
    (J (r e => p = Eq.trans (Eq.sym (DecEq.canon (DecEq.decide [decEq := decEq] x x) rfl)) r)
      (DecEq.fromCanon x y p) (DecEq.canonConst (DecEq.decide [decEq := decEq] x y) p q))
    (J (z e => z = q) rfl (DecEq.fromCanon x y q))

-- Orderings (docs/proposals/interfaces.md §6.2)

-- The comparison the other way round.
def Ordering.flip: Ordering -> Ordering
  | Less    => Greater
  | Equal   => Equal
  | Greater => Less

theorem Ordering.lessNotEqual: Not (Less = Equal)
  | p => Nat.zeroNotSucc 0 (Eq.cong Ordering.index p)

theorem Ordering.lessNotGreater: Not (Less = Greater)
  | p => Nat.zeroNotSucc 1 (Eq.cong Ordering.index p)

theorem Ordering.equalNotLess: Not (Equal = Less)
  | p => Nat.zeroNotSucc 0 (Eq.sym (Eq.cong Ordering.index p))

theorem Ordering.equalNotGreater: Not (Equal = Greater)
  | p => Nat.zeroNotSucc 0 (Nat.succInjective 0 1 (Eq.cong Ordering.index p))

theorem Ordering.greaterNotLess: Not (Greater = Less)
  | p => Nat.zeroNotSucc 1 (Eq.sym (Eq.cong Ordering.index p))

theorem Ordering.greaterNotEqual: Not (Greater = Equal)
  | p => Nat.zeroNotSucc 0 (Nat.succInjective 0 1 (Eq.sym (Eq.cong Ordering.index p)))

theorem Ordering.indexInjective: (c: Ordering) -> (d: Ordering) -> Ordering.index c = Ordering.index d -> c = d
  | Less,    Less,    h => rfl
  | Less,    Equal,   h => Void.exfalso (Nat.zeroNotSucc 0 h)
  | Less,    Greater, h => Void.exfalso (Nat.zeroNotSucc 1 h)
  | Equal,   Less,    h => Void.exfalso (Nat.succNotZero 0 h)
  | Equal,   Equal,   h => rfl
  | Equal,   Greater, h => Void.exfalso (Nat.zeroNotSucc 0 (Nat.succInjective 0 1 h))
  | Greater, Less,    h => Void.exfalso (Nat.succNotZero 1 h)
  | Greater, Equal,   h => Void.exfalso (Nat.succNotZero 0 (Nat.succInjective 1 0 h))
  | Greater, Greater, h => rfl

-- A comparison that's its own opposite is `Equal`.
theorem Ordering.flipSelf: (c: Ordering) -> c = Ordering.flip c -> c = Equal
  | Less,    h => Void.exfalso (Ordering.lessNotGreater h)
  | Equal,   h => rfl
  | Greater, h => Void.exfalso (Ordering.greaterNotLess h)

theorem Ordering.andThenEqual: (c: Ordering) -> (d: Ordering) -> Ordering.andThen c d = Equal -> And (c = Equal) (d = Equal)
  | Less,    d, h => Void.exfalso (Ordering.lessNotEqual h)
  | Equal,   d, h => Both rfl h
  | Greater, d, h => Void.exfalso (Ordering.greaterNotEqual h)

theorem Ordering.flipAndThen: (c: Ordering) -> (d: Ordering) ->
    Ordering.flip (Ordering.andThen c d) = Ordering.andThen (Ordering.flip c) (Ordering.flip d)
  | Less,    d => rfl
  | Equal,   d => rfl
  | Greater, d => rfl

-- `Less` is transitive for `c1` then `r1` (lexicographic), given that it
-- is for the first comparisons and for the rest, and that an `Equal` first
-- comparison passes the other one on.
theorem Ordering.andThenTrans: (c1: Ordering) -> (c2: Ordering) -> (c3: Ordering) ->
    (r1: Ordering) -> (r2: Ordering) -> (r3: Ordering) ->
    (c1 = Less -> c2 = Less -> c3 = Less) -> (c1 = Equal -> c3 = c2) -> (c2 = Equal -> c3 = c1) ->
    (r1 = Less -> r2 = Less -> r3 = Less) ->
    Ordering.andThen c1 r1 = Less -> Ordering.andThen c2 r2 = Less -> Ordering.andThen c3 r3 = Less
  | Less,    Less,    c3, r1, r2, r3, t, e1, e2, tr, h1, h2 => rewrite t rfl rfl in rfl
  | Less,    Equal,   c3, r1, r2, r3, t, e1, e2, tr, h1, h2 => rewrite e2 rfl in rfl
  | Less,    Greater, c3, r1, r2, r3, t, e1, e2, tr, h1, h2 => Void.exfalso (Ordering.greaterNotLess h2)
  | Equal,   Less,    c3, r1, r2, r3, t, e1, e2, tr, h1, h2 => rewrite e1 rfl in rfl
  | Equal,   Equal,   c3, r1, r2, r3, t, e1, e2, tr, h1, h2 => rewrite e1 rfl in tr h1 h2
  | Equal,   Greater, c3, r1, r2, r3, t, e1, e2, tr, h1, h2 => Void.exfalso (Ordering.greaterNotLess h2)
  | Greater, c2,      c3, r1, r2, r3, t, e1, e2, tr, h1, h2 => Void.exfalso (Ordering.greaterNotLess h1)

-- `Nat.compare` steps down both numbers together, so its laws are proved by
-- recursion on both.
theorem Nat.compareSucc (m: Nat) (n: Nat): Nat.compare (Succ m) (Succ n) = Nat.compare m n := rfl

theorem Nat.compareEqual: (m: Nat) -> (n: Nat) -> Nat.compare m n = Equal -> m = n
  | Zero,   Zero,   h => rfl
  | Zero,   Succ n, h => Void.exfalso (Ordering.lessNotEqual h)
  | Succ m, Zero,   h => Void.exfalso (Ordering.greaterNotEqual h)
  | Succ m, Succ n, h => Eq.cong Succ (Nat.compareEqual m n h)

theorem Nat.compareFlip: (m: Nat) -> (n: Nat) -> Nat.compare n m = Ordering.flip (Nat.compare m n)
  | Zero,   Zero   => rfl
  | Zero,   Succ n => rfl
  | Succ m, Zero   => rfl
  | Succ m, Succ n => Nat.compareFlip m n

theorem Nat.compareTrans: (x: Nat) -> (y: Nat) -> (z: Nat) ->
    Nat.compare x y = Less -> Nat.compare y z = Less -> Nat.compare x z = Less
  | Zero,   Zero,   z,      h1, h2 => Void.exfalso (Ordering.equalNotLess h1)
  | Zero,   Succ y, Zero,   h1, h2 => Void.exfalso (Ordering.greaterNotLess h2)
  | Zero,   Succ y, Succ z, h1, h2 => rfl
  | Succ x, Zero,   z,      h1, h2 => Void.exfalso (Ordering.greaterNotLess h1)
  | Succ x, Succ y, Zero,   h1, h2 => Void.exfalso (Ordering.greaterNotLess h2)
  | Succ x, Succ y, Succ z, h1, h2 => Nat.compareTrans x y z h1 h2

theorem Nat.lessOfCompare: (m: Nat) -> (n: Nat) -> Nat.compare m n = Less -> m < n
  | Zero,   Zero,   h => Void.exfalso (Ordering.equalNotLess h)
  | Zero,   Succ n, h => rfl
  | Succ m, Zero,   h => Void.exfalso (Ordering.greaterNotLess h)
  | Succ m, Succ n, h => Nat.lessOfCompare m n h

theorem Nat.compareOfLess: (m: Nat) -> (n: Nat) -> m < n -> Nat.compare m n = Less
  | m,      Zero,   h => Void.exfalso (Bool.falseNotTrue h)
  | Zero,   Succ n, h => rfl
  | Succ m, Succ n, h => Nat.compareOfLess m n h

theorem Nat.leOfCompare: (m: Nat) -> (n: Nat) -> Not (Nat.compare m n = Greater) -> m <= n
  | Zero,   n,      h => rfl
  | Succ m, Zero,   h => Void.exfalso (h rfl)
  | Succ m, Succ n, h => Nat.leOfCompare m n h

theorem Nat.compareOfLe: (m: Nat) -> (n: Nat) -> m <= n -> Not (Nat.compare m n = Greater)
  | Zero,   Zero,   h, e => Ordering.equalNotGreater e
  | Zero,   Succ n, h, e => Ordering.lessNotGreater e
  | Succ m, Zero,   h, e => Bool.falseNotTrue h
  | Succ m, Succ n, h, e => Nat.compareOfLe m n h e

theorem Int.compareEqual: (a: Int) -> (b: Int) -> Int.compare a b = Equal -> a = b
  | OfNat m,   OfNat n,   h => Eq.cong OfNat (Nat.compareEqual m n h)
  | OfNat m,   NegSucc n, h => Void.exfalso (Ordering.greaterNotEqual h)
  | NegSucc m, OfNat n,   h => Void.exfalso (Ordering.lessNotEqual h)
  | NegSucc m, NegSucc n, h => Eq.cong NegSucc (Eq.sym (Nat.compareEqual n m h))

theorem Int.compareFlip: (a: Int) -> (b: Int) -> Int.compare b a = Ordering.flip (Int.compare a b)
  | OfNat m,   OfNat n   => Nat.compareFlip m n
  | OfNat m,   NegSucc n => rfl
  | NegSucc m, OfNat n   => rfl
  | NegSucc m, NegSucc n => Nat.compareFlip n m

theorem Int.compareTrans: (a: Int) -> (b: Int) -> (c: Int) ->
    Int.compare a b = Less -> Int.compare b c = Less -> Int.compare a c = Less
  | OfNat x,   OfNat y,   OfNat z,   h1, h2 => Nat.compareTrans x y z h1 h2
  | OfNat x,   OfNat y,   NegSucc z, h1, h2 => Void.exfalso (Ordering.greaterNotLess h2)
  | OfNat x,   NegSucc y, c,         h1, h2 => Void.exfalso (Ordering.greaterNotLess h1)
  | NegSucc x, OfNat y,   OfNat z,   h1, h2 => rfl
  | NegSucc x, OfNat y,   NegSucc z, h1, h2 => Void.exfalso (Ordering.greaterNotLess h2)
  | NegSucc x, NegSucc y, OfNat z,   h1, h2 => rfl
  | NegSucc x, NegSucc y, NegSucc z, h1, h2 => Nat.compareTrans z y x h2 h1

theorem Int.lessOfCompare: (a: Int) -> (b: Int) -> Int.compare a b = Less -> Int.LessThan a b
  | OfNat m,   OfNat n,   h => Nat.lessOfCompare m n h
  | OfNat m,   NegSucc n, h => Void.exfalso (Ordering.greaterNotLess h)
  | NegSucc m, OfNat n,   h => rfl
  | NegSucc m, NegSucc n, h => Nat.lessOfCompare n m h

theorem Int.compareOfLess: (a: Int) -> (b: Int) -> Int.LessThan a b -> Int.compare a b = Less
  | OfNat m,   OfNat n,   h => Nat.compareOfLess m n h
  | OfNat m,   NegSucc n, h => Void.exfalso (Bool.falseNotTrue h)
  | NegSucc m, OfNat n,   h => rfl
  | NegSucc m, NegSucc n, h => Nat.compareOfLess n m h

theorem Int.leOfCompare: (a: Int) -> (b: Int) -> Not (Int.compare a b = Greater) -> Int.LessEq a b
  | OfNat m,   OfNat n,   h => Nat.leOfCompare m n h
  | OfNat m,   NegSucc n, h => Void.exfalso (h rfl)
  | NegSucc m, OfNat n,   h => rfl
  | NegSucc m, NegSucc n, h => Nat.leOfCompare n m h

theorem Int.compareOfLe: (a: Int) -> (b: Int) -> Int.LessEq a b -> Not (Int.compare a b = Greater)
  | OfNat m,   OfNat n,   h, e => Nat.compareOfLe m n h e
  | OfNat m,   NegSucc n, h, e => Bool.falseNotTrue h
  | NegSucc m, OfNat n,   h, e => Ordering.lessNotGreater e
  | NegSucc m, NegSucc n, h, e => Nat.compareOfLe n m h e

-- Lexicographic comparison of lists, by a comparison of their elements:
-- the first difference decides, and a list comes before its extensions.
def List.compareLex (cmp: a -> a -> Ordering): List a -> List a -> Ordering
  | Nil,       Nil       => Equal
  | Nil,       Cons y ys => Less
  | Cons x xs, Nil       => Greater
  | Cons x xs, Cons y ys => Ordering.andThen (cmp x y) (List.compareLex cmp xs ys)

theorem List.compareLexEqual (cmp: a -> a -> Ordering) (equal: (x: a) -> (y: a) -> cmp x y = Equal -> x = y):
    (xs: List a) -> (ys: List a) -> List.compareLex cmp xs ys = Equal -> xs = ys
  | Nil,       Nil,       h => rfl
  | Nil,       Cons y ys, h => Void.exfalso (Ordering.lessNotEqual h)
  | Cons x xs, Nil,       h => Void.exfalso (Ordering.greaterNotEqual h)
  | Cons x xs, Cons y ys, h =>
    Eq.trans (Eq.cong (t => Cons t xs) (equal x y (And.left (Ordering.andThenEqual (cmp x y) (List.compareLex cmp xs ys) h))))
      (Eq.cong (Cons y) (List.compareLexEqual cmp equal xs ys (And.right (Ordering.andThenEqual (cmp x y) (List.compareLex cmp xs ys) h))))

theorem List.compareLexFlip (cmp: a -> a -> Ordering) (flip: (x: a) -> (y: a) -> cmp y x = Ordering.flip (cmp x y)):
    (xs: List a) -> (ys: List a) -> List.compareLex cmp ys xs = Ordering.flip (List.compareLex cmp xs ys)
  | Nil,       Nil       => rfl
  | Nil,       Cons y ys => rfl
  | Cons x xs, Nil       => rfl
  | Cons x xs, Cons y ys =>
    rewrite flip x y, List.compareLexFlip cmp flip xs ys in
      Eq.sym (Ordering.flipAndThen (cmp x y) (List.compareLex cmp xs ys))

theorem List.compareLexTrans (cmp: a -> a -> Ordering) (equal: (x: a) -> (y: a) -> cmp x y = Equal -> x = y)
    (trans: (x: a) -> (y: a) -> (z: a) -> cmp x y = Less -> cmp y z = Less -> cmp x z = Less):
    (xs: List a) -> (ys: List a) -> (zs: List a) ->
    List.compareLex cmp xs ys = Less -> List.compareLex cmp ys zs = Less -> List.compareLex cmp xs zs = Less
  | Nil,       Nil,       zs,        h1, h2 => Void.exfalso (Ordering.equalNotLess h1)
  | Nil,       Cons y ys, Nil,       h1, h2 => Void.exfalso (Ordering.greaterNotLess h2)
  | Nil,       Cons y ys, Cons z zs, h1, h2 => rfl
  | Cons x xs, Nil,       zs,        h1, h2 => Void.exfalso (Ordering.greaterNotLess h1)
  | Cons x xs, Cons y ys, Nil,       h1, h2 => Void.exfalso (Ordering.greaterNotLess h2)
  | Cons x xs, Cons y ys, Cons z zs, h1, h2 =>
    Ordering.andThenTrans (cmp x y) (cmp y z) (cmp x z)
      (List.compareLex cmp xs ys) (List.compareLex cmp ys zs) (List.compareLex cmp xs zs)
      (trans x y z)
      (e => Eq.cong (t => cmp t z) (equal x y e))
      (e => Eq.sym (Eq.cong (t => cmp x t) (equal y z e)))
      (p q => List.compareLexTrans cmp equal trans xs ys zs p q) h1 h2

-- Pairs, by their first parts, then their second.
def Pair.compareWith (ca: a -> a -> Ordering) (cb: b -> b -> Ordering): Pair a b -> Pair a b -> Ordering
  | MkPair x1 y1, MkPair x2 y2 => Ordering.andThen (ca x1 x2) (cb y1 y2)

theorem Pair.compareWithEqual (ca: a -> a -> Ordering) (cb: b -> b -> Ordering)
    (ea: (x: a) -> (y: a) -> ca x y = Equal -> x = y) (eb: (x: b) -> (y: b) -> cb x y = Equal -> x = y):
    (p: Pair a b) -> (q: Pair a b) -> Pair.compareWith ca cb p q = Equal -> p = q
  | MkPair x1 y1, MkPair x2 y2, h =>
    Eq.trans (Eq.cong (t => MkPair t y1) (ea x1 x2 (And.left (Ordering.andThenEqual (ca x1 x2) (cb y1 y2) h))))
      (Eq.cong (MkPair x2) (eb y1 y2 (And.right (Ordering.andThenEqual (ca x1 x2) (cb y1 y2) h))))

theorem Pair.compareWithFlip (ca: a -> a -> Ordering) (cb: b -> b -> Ordering)
    (fa: (x: a) -> (y: a) -> ca y x = Ordering.flip (ca x y)) (fb: (x: b) -> (y: b) -> cb y x = Ordering.flip (cb x y)):
    (p: Pair a b) -> (q: Pair a b) -> Pair.compareWith ca cb q p = Ordering.flip (Pair.compareWith ca cb p q)
  | MkPair x1 y1, MkPair x2 y2 =>
    rewrite fa x1 x2, fb y1 y2 in Eq.sym (Ordering.flipAndThen (ca x1 x2) (cb y1 y2))

theorem Pair.compareWithTrans (ca: a -> a -> Ordering) (cb: b -> b -> Ordering)
    (ea: (x: a) -> (y: a) -> ca x y = Equal -> x = y)
    (ta: (x: a) -> (y: a) -> (z: a) -> ca x y = Less -> ca y z = Less -> ca x z = Less)
    (tb: (x: b) -> (y: b) -> (z: b) -> cb x y = Less -> cb y z = Less -> cb x z = Less):
    (p: Pair a b) -> (q: Pair a b) -> (r: Pair a b) ->
    Pair.compareWith ca cb p q = Less -> Pair.compareWith ca cb q r = Less -> Pair.compareWith ca cb p r = Less
  | MkPair x1 y1, MkPair x2 y2, MkPair x3 y3, h1, h2 =>
    Ordering.andThenTrans (ca x1 x2) (ca x2 x3) (ca x1 x3) (cb y1 y2) (cb y2 y3) (cb y1 y3)
      (ta x1 x2 x3)
      (e => Eq.cong (t => ca t x3) (ea x1 x2 e))
      (e => Eq.sym (Eq.cong (t => ca x1 t) (ea x2 x3 e)))
      (tb y1 y2 y3) h1 h2

-- Optional values: `Nothing` first.
def Maybe.compareWith (cmp: a -> a -> Ordering): Maybe a -> Maybe a -> Ordering
  | Nothing, Nothing => Equal
  | Nothing, Just y  => Less
  | Just x,  Nothing => Greater
  | Just x,  Just y  => cmp x y

theorem Maybe.compareWithEqual (cmp: a -> a -> Ordering) (equal: (x: a) -> (y: a) -> cmp x y = Equal -> x = y):
    (m: Maybe a) -> (n: Maybe a) -> Maybe.compareWith cmp m n = Equal -> m = n
  | Nothing, Nothing, h => rfl
  | Nothing, Just y,  h => Void.exfalso (Ordering.lessNotEqual h)
  | Just x,  Nothing, h => Void.exfalso (Ordering.greaterNotEqual h)
  | Just x,  Just y,  h => Eq.cong Just (equal x y h)

theorem Maybe.compareWithFlip (cmp: a -> a -> Ordering) (flip: (x: a) -> (y: a) -> cmp y x = Ordering.flip (cmp x y)):
    (m: Maybe a) -> (n: Maybe a) -> Maybe.compareWith cmp n m = Ordering.flip (Maybe.compareWith cmp m n)
  | Nothing, Nothing => rfl
  | Nothing, Just y  => rfl
  | Just x,  Nothing => rfl
  | Just x,  Just y  => flip x y

theorem Maybe.compareWithTrans (cmp: a -> a -> Ordering)
    (trans: (x: a) -> (y: a) -> (z: a) -> cmp x y = Less -> cmp y z = Less -> cmp x z = Less):
    (m: Maybe a) -> (n: Maybe a) -> (o: Maybe a) ->
    Maybe.compareWith cmp m n = Less -> Maybe.compareWith cmp n o = Less -> Maybe.compareWith cmp m o = Less
  | Nothing, Nothing, o,       h1, h2 => Void.exfalso (Ordering.equalNotLess h1)
  | Nothing, Just y,  Nothing, h1, h2 => Void.exfalso (Ordering.greaterNotLess h2)
  | Nothing, Just y,  Just z,  h1, h2 => rfl
  | Just x,  Nothing, o,       h1, h2 => Void.exfalso (Ordering.greaterNotLess h1)
  | Just x,  Just y,  Nothing, h1, h2 => Void.exfalso (Ordering.greaterNotLess h2)
  | Just x,  Just y,  Just z,  h1, h2 => trans x y z h1 h2

-- Characters, by scalar value.
def Char.compare (x: Char) (y: Char): Ordering := Nat.compare (Char.toNat x) (Char.toNat y)

theorem Char.compareEqual (x: Char) (y: Char) (h: Char.compare x y = Equal): x = y :=
  Char.ext x y (Nat.compareEqual (Char.toNat x) (Char.toNat y) h)

theorem Char.compareFlip (x: Char) (y: Char): Char.compare y x = Ordering.flip (Char.compare x y) :=
  Nat.compareFlip (Char.toNat x) (Char.toNat y)

theorem Char.compareTrans (x: Char) (y: Char) (z: Char) (h1: Char.compare x y = Less) (h2: Char.compare y z = Less):
    Char.compare x z = Less :=
  Nat.compareTrans (Char.toNat x) (Char.toNat y) (Char.toNat z) h1 h2

-- `Text.compare` is lexicographic by characters: `List.compareLex` with
-- `Char.compare`, step for step. So its laws are the list's.
theorem Text.compareCharsLex: (xs: List Char) -> (ys: List Char) -> Text.compareChars xs ys = List.compareLex Char.compare xs ys
  | Nil,       Nil       => rfl
  | Nil,       Cons y ys => rfl
  | Cons x xs, Nil       => rfl
  | Cons x xs, Cons y ys => Eq.cong (r => Ordering.andThen (Char.compare x y) r) (Text.compareCharsLex xs ys)

theorem Text.ext: (s: Text) -> (t: Text) -> Text.toList s = Text.toList t -> s = t
  | MkText a, MkText b, h => Eq.cong MkText h

theorem Text.compareEqual (s: Text) (t: Text) (h: Text.compare s t = Equal): s = t :=
  Text.ext s t (List.compareLexEqual Char.compare Char.compareEqual (Text.toList s) (Text.toList t)
    (Eq.trans (Eq.sym (Text.compareCharsLex (Text.toList s) (Text.toList t))) h))

theorem Text.compareFlip (s: Text) (t: Text): Text.compare t s = Ordering.flip (Text.compare s t) :=
  Eq.trans (Text.compareCharsLex (Text.toList t) (Text.toList s))
    (Eq.trans (List.compareLexFlip Char.compare Char.compareFlip (Text.toList s) (Text.toList t))
      (Eq.cong Ordering.flip (Eq.sym (Text.compareCharsLex (Text.toList s) (Text.toList t)))))

theorem Text.compareTrans (s: Text) (t: Text) (u: Text) (h1: Text.compare s t = Less) (h2: Text.compare t u = Less):
    Text.compare s u = Less :=
  Eq.trans (Text.compareCharsLex (Text.toList s) (Text.toList u))
    (List.compareLexTrans Char.compare Char.compareEqual Char.compareTrans (Text.toList s) (Text.toList t) (Text.toList u)
      (Eq.trans (Eq.sym (Text.compareCharsLex (Text.toList s) (Text.toList t))) h1)
      (Eq.trans (Eq.sym (Text.compareCharsLex (Text.toList t) (Text.toList u))) h2))

theorem Bool.toNatInjective: (a: Bool) -> (b: Bool) -> Bool.toNat a = Bool.toNat b -> a = b
  | False, False, h => rfl
  | False, True,  h => Void.exfalso (Nat.zeroNotSucc 0 h)
  | True,  False, h => Void.exfalso (Nat.succNotZero 0 h)
  | True,  True,  h => rfl

-- `False` first.
def Bool.compare (a: Bool) (b: Bool): Ordering := Nat.compare (Bool.toNat a) (Bool.toNat b)

-- `Less`, `Equal`, `Greater`.
def Ordering.compare (c: Ordering) (d: Ordering): Ordering := Nat.compare (Ordering.index c) (Ordering.index d)

-- A total order: a comparison with its laws, and the relations `<` and `<=`
-- with their decisions, agreeing with it (docs/proposals/interfaces.md
-- §6.2, D180; the fields are `lessThan` and `lessEq`, D200). The relations
-- are fields so that `Nat`'s can be `Nat.LessThan` and `Nat.LessEq`
-- themselves. Build one with `Ord.fromCompare` or `Ord.byKey`.
interface Ord (a: Type) =
  { eq: DecEq a
  , compare: a -> a -> Ordering
  , lessThan: a -> a -> Prop
  , lessEq: a -> a -> Prop
  , decLessThan: (x: a) -> (y: a) -> Decidable (lessThan x y)
  , decLessEq: (x: a) -> (y: a) -> Decidable (lessEq x y)
  -- `Equal` means equal; the other way round is the opposite; `Less` is
  -- transitive.
  , equal: (x: a) -> (y: a) -> compare x y = Equal -> x = y
  , flip: (x: a) -> (y: a) -> compare y x = Ordering.flip (compare x y)
  , trans: (x: a) -> (y: a) -> (z: a) -> compare x y = Less -> compare y z = Less -> compare x z = Less
  -- The relations agree with `compare`.
  , lessThanOf: (x: a) -> (y: a) -> compare x y = Less -> lessThan x y
  , lessThanTo: (x: a) -> (y: a) -> lessThan x y -> compare x y = Less
  , lessEqOf: (x: a) -> (y: a) -> Not (compare x y = Greater) -> lessEq x y
  , lessEqTo: (x: a) -> (y: a) -> lessEq x y -> Not (compare x y = Greater)
  }

-- From a comparison and its three laws. The relations are
-- `compare x y = Less` and `Not (compare x y = Greater)`, decided through
-- `DecEq Ordering`. `eq` is the `decEq` given.
def Ord.fromCompare [auto decEq: DecEq a] (compare: a -> a -> Ordering)
    (equal: (x: a) -> (y: a) -> compare x y = Equal -> x = y)
    (flip: (x: a) -> (y: a) -> compare y x = Ordering.flip (compare x y))
    (trans: (x: a) -> (y: a) -> (z: a) -> compare x y = Less -> compare y z = Less -> compare x z = Less): Ord a :=
  { compare = compare
  , lessThan = x y => compare x y = Less
  , lessEq = x y => Not (compare x y = Greater)
  , decLessThan = x y => Ordering.decEq (compare x y) Less
  , decLessEq = x y => Decidable.not (Ordering.decEq (compare x y) Greater)
  , equal = equal
  , flip = flip
  , trans = trans
  , lessThanOf = x y h => h
  , lessThanTo = x y h => h
  , lessEqOf = x y h => h
  , lessEqTo = x y h => h
  }

-- Orders `a` by a key, given that the key tells values apart.
def Ord.byKey [auto decEq: DecEq a] [auto ord: Ord b] (key: a -> b)
    (inj: (x: a) -> (y: a) -> key x = key y -> x = y): Ord a :=
  Ord.fromCompare (x y => Ord.compare (key x) (key y))
    (x y h => inj x y (ord.equal (key x) (key y) h))
    (x y => ord.flip (key x) (key y))
    (x y z => ord.trans (key x) (key y) (key z))

-- The larger, and the smaller (the first, if they're equal).
def Ord.max [auto ord: Ord a] (x: a) (y: a): a := match Ord.compare x y with
  | Less => y
  | _    => x

def Ord.min [auto ord: Ord a] (x: a) (y: a): a := match Ord.compare x y with
  | Greater => y
  | _       => x

-- Anything compares `Equal` with itself.
theorem Ord.compareSelf [auto ord: Ord a] (x: a): Ord.compare x x = Equal :=
  Ordering.flipSelf (Ord.compare x x) (ord.flip x x)

instance Nat.instOrd: Ord Nat :=
  { compare = Nat.compare
  , lessThan = Nat.LessThan
  , lessEq = Nat.LessEq
  , decLessThan = Nat.decLessThan
  , decLessEq = Nat.decLessEq
  , equal = Nat.compareEqual
  , flip = Nat.compareFlip
  , trans = Nat.compareTrans
  , lessThanOf = Nat.lessOfCompare
  , lessThanTo = Nat.compareOfLess
  , lessEqOf = Nat.leOfCompare
  , lessEqTo = Nat.compareOfLe
  }

instance Int.instOrd: Ord Int :=
  { compare = Int.compare
  , lessThan = Int.LessThan
  , lessEq = Int.LessEq
  , decLessThan = Int.decLessThan
  , decLessEq = Int.decLessEq
  , equal = Int.compareEqual
  , flip = Int.compareFlip
  , trans = Int.compareTrans
  , lessThanOf = Int.lessOfCompare
  , lessThanTo = Int.compareOfLess
  , lessEqOf = Int.leOfCompare
  , lessEqTo = Int.compareOfLe
  }

instance Char.instOrd: Ord Char :=
  Ord.fromCompare Char.compare Char.compareEqual Char.compareFlip Char.compareTrans

instance Text.instOrd: Ord Text :=
  Ord.fromCompare Text.compare Text.compareEqual Text.compareFlip Text.compareTrans

instance Bool.instOrd: Ord Bool :=
  Ord.fromCompare Bool.compare
    (x y h => Bool.toNatInjective x y (Nat.compareEqual (Bool.toNat x) (Bool.toNat y) h))
    (x y => Nat.compareFlip (Bool.toNat x) (Bool.toNat y))
    (x y z => Nat.compareTrans (Bool.toNat x) (Bool.toNat y) (Bool.toNat z))

instance Ordering.instOrd: Ord Ordering :=
  Ord.fromCompare Ordering.compare
    (x y h => Ordering.indexInjective x y (Nat.compareEqual (Ordering.index x) (Ordering.index y) h))
    (x y => Nat.compareFlip (Ordering.index x) (Ordering.index y))
    (x y z => Nat.compareTrans (Ordering.index x) (Ordering.index y) (Ordering.index z))

instance List.instOrd [auto ord: Ord a]: Ord (List a) :=
  Ord.fromCompare (List.compareLex Ord.compare)
    (List.compareLexEqual Ord.compare ord.equal)
    (List.compareLexFlip Ord.compare ord.flip)
    (List.compareLexTrans Ord.compare ord.equal ord.trans)

instance Maybe.instOrd [auto ord: Ord a]: Ord (Maybe a) :=
  Ord.fromCompare (Maybe.compareWith Ord.compare)
    (Maybe.compareWithEqual Ord.compare ord.equal)
    (Maybe.compareWithFlip Ord.compare ord.flip)
    (Maybe.compareWithTrans Ord.compare ord.trans)

instance Pair.instOrd [auto ordA: Ord a] [auto ordB: Ord b]: Ord (Pair a b) :=
  Ord.fromCompare (Pair.compareWith Ord.compare Ord.compare)
    (Pair.compareWithEqual Ord.compare Ord.compare ordA.equal ordB.equal)
    (Pair.compareWithFlip Ord.compare Ord.compare ordA.flip ordB.flip)
    (Pair.compareWithTrans Ord.compare Ord.compare ordA.equal ordA.trans ordB.trans)

-- Arithmetic laws (docs/proposals/interfaces.md §5.13, D187): what the
-- `Add` and `Mul` instances for `Nat` and `Int` need. They come before the
-- instances, and their `+` and `*` are the primitive operations.

theorem Nat.addZero: (n: Nat) -> n + 0 = n
  | Zero => rfl
  | Succ n => Eq.cong Succ (Nat.addZero n)

theorem Nat.addSucc: (n: Nat) -> (m: Nat) -> n + Succ m = Succ (n + m)
  | Zero, m => rfl
  | Succ n, m => Eq.cong Succ (Nat.addSucc n m)

theorem Nat.addComm: (m: Nat) -> (n: Nat) -> m + n = n + m
  | Zero, n => Eq.sym (Nat.addZero n)
  | Succ m, n => Eq.trans (Eq.cong Succ (Nat.addComm m n)) (Eq.sym (Nat.addSucc n m))

theorem Nat.addAssoc: (a: Nat) -> (b: Nat) -> (c: Nat) -> (a + b) + c = a + (b + c)
  | Zero, b, c => rfl
  | Succ a, b, c => Eq.cong Succ (Nat.addAssoc a b c)

theorem Nat.mulZero: (n: Nat) -> n * 0 = 0
  | Zero => rfl
  | Succ n => Nat.mulZero n

theorem Nat.mulOne: (n: Nat) -> n * 1 = n
  | Zero => rfl
  | Succ n => Eq.cong Succ (Nat.mulOne n)

theorem Nat.mulSucc: (n: Nat) -> (m: Nat) -> n * Succ m = n + n * m
  | Zero, m => rfl
  | Succ n, m => Eq.cong Succ (Eq.trans (Eq.cong (t => m + t) (Nat.mulSucc n m)) (Eq.trans (Eq.sym (Nat.addAssoc m n (n * m))) (Eq.trans (Eq.cong (t => t + n * m) (Nat.addComm m n)) (Nat.addAssoc n m (n * m)))))

theorem Nat.mulComm: (n: Nat) -> (m: Nat) -> n * m = m * n
  | Zero, m => Eq.sym (Nat.mulZero m)
  | Succ n, m => Eq.trans (Eq.cong (t => m + t) (Nat.mulComm n m)) (Eq.sym (Nat.mulSucc m n))

theorem Nat.mulDistribRight: (a: Nat) -> (b: Nat) -> (c: Nat) -> (a + b) * c = a * c + b * c
  | Zero, b, c => rfl
  | Succ a, b, c => Eq.trans (Eq.cong (t => c + t) (Nat.mulDistribRight a b c)) (Eq.sym (Nat.addAssoc c (a * c) (b * c)))

theorem Nat.mulAssoc: (a: Nat) -> (b: Nat) -> (c: Nat) -> (a * b) * c = a * (b * c)
  | Zero, b, c => rfl
  | Succ a, b, c => Eq.trans (Nat.mulDistribRight b (a * b) c) (Eq.cong (t => b * c + t) (Nat.mulAssoc a b c))

-- Addition laws, after Lean's core: case analysis on the constructors plus
-- lemmas about `Int.subNatNat`.
theorem Int.subNatNatZeroRight: (m: Nat) -> Int.subNatNat m 0 = OfNat m
  | Zero   => rfl
  | Succ m => rfl

theorem Int.subNatNatFromSucc (m: Nat) (n: Nat): (t: Nat) ->
    Int.subNatNatFrom (Succ m) (Succ n) t = Int.subNatNatFrom m n t
  | Zero   => rfl
  | Succ t => rfl

theorem Int.subNatNatSucc (m: Nat) (n: Nat): Int.subNatNat (Succ m) (Succ n) = Int.subNatNat m n := Int.subNatNatFromSucc m n (n - m)

theorem Int.addZero: (a: Int) -> Int.add a (OfNat 0) = a
  | OfNat m   => Eq.cong OfNat (Nat.addZero m)
  | NegSucc m => rfl

theorem Int.zeroAdd: (a: Int) -> Int.add (OfNat 0) a = a
  | OfNat m   => rfl
  | NegSucc m => rfl

theorem Int.addComm: (a: Int) -> (b: Int) -> Int.add a b = Int.add b a
  | OfNat m,   OfNat n   => Eq.cong OfNat (Nat.addComm m n)
  | OfNat m,   NegSucc n => rfl
  | NegSucc m, OfNat n   => rfl
  | NegSucc m, NegSucc n => Eq.cong (t => NegSucc (Succ t)) (Nat.addComm m n)

-- Adding a natural number to a difference.
theorem Int.ofNatAddSubNatNat (k: Nat): (m: Nat) -> (n: Nat) ->
    Int.add (OfNat k) (Int.subNatNat m n) = Int.subNatNat (m + k) n
  | Zero,   Zero   =>
    Eq.trans (Eq.cong OfNat (Nat.addZero k)) (Eq.sym (Int.subNatNatZeroRight k))
  | Zero,   Succ n => rfl
  | Succ m, Zero   =>
    Eq.trans (Eq.cong OfNat (Eq.trans (Nat.addSucc k m) (Eq.cong Succ (Nat.addComm k m))))
             (Eq.sym (Int.subNatNatZeroRight (Succ (m + k))))
  | Succ m, Succ n =>
    Eq.trans (Eq.cong (Int.add (OfNat k)) (Int.subNatNatSucc m n))
      (Eq.trans (Int.ofNatAddSubNatNat k m n) (Eq.sym (Int.subNatNatSucc (m + k) n)))

theorem Int.subNatNatAddOfNat (k: Nat) (m: Nat) (n: Nat):
    Int.add (Int.subNatNat m n) (OfNat k) = Int.subNatNat (m + k) n :=
  Eq.trans (Int.addComm (Int.subNatNat m n) (OfNat k)) (Int.ofNatAddSubNatNat k m n)

-- Adding a negative number to a difference.
theorem Int.negSuccAddSubNatNat (k: Nat): (m: Nat) -> (n: Nat) ->
    Int.add (NegSucc k) (Int.subNatNat m n) = Int.subNatNat m (Succ (n + k))
  | Zero,   Zero   => rfl
  | Zero,   Succ n => Eq.cong (t => NegSucc (Succ t)) (Nat.addComm k n)
  | Succ m, Zero   => rfl
  | Succ m, Succ n =>
    Eq.trans (Eq.cong (Int.add (NegSucc k)) (Int.subNatNatSucc m n))
      (Eq.trans (Int.negSuccAddSubNatNat k m n) (Eq.sym (Int.subNatNatSucc m (Succ (n + k)))))

theorem Int.subNatNatAddNegSucc (k: Nat) (m: Nat) (n: Nat):
    Int.add (Int.subNatNat m n) (NegSucc k) = Int.subNatNat m (Succ (n + k)) :=
  Eq.trans (Int.addComm (Int.subNatNat m n) (NegSucc k)) (Int.negSuccAddSubNatNat k m n)

theorem Int.addAssoc: (a: Int) -> (b: Int) -> (c: Int) ->
    Int.add (Int.add a b) c = Int.add a (Int.add b c)
  | OfNat a,   OfNat b,   OfNat c   => Eq.cong OfNat (Nat.addAssoc a b c)
  | OfNat a,   OfNat b,   NegSucc c =>
    Eq.trans (Eq.cong (t => Int.subNatNat t (Succ c)) (Nat.addComm a b))
             (Eq.sym (Int.ofNatAddSubNatNat a b (Succ c)))
  | OfNat a,   NegSucc b, OfNat c   =>
    Eq.trans (Int.subNatNatAddOfNat c a (Succ b))
      (Eq.trans (Eq.cong (t => Int.subNatNat t (Succ b)) (Nat.addComm a c))
                (Eq.sym (Int.ofNatAddSubNatNat a c (Succ b))))
  | NegSucc a, OfNat b,   OfNat c   => Int.subNatNatAddOfNat c b (Succ a)
  | OfNat a,   NegSucc b, NegSucc c => Int.subNatNatAddNegSucc c a (Succ b)
  | NegSucc a, OfNat b,   NegSucc c =>
    Eq.trans (Int.subNatNatAddNegSucc c b (Succ a))
      (Eq.trans (Eq.cong (t => Int.subNatNat b (Succ (Succ t))) (Nat.addComm a c))
                (Eq.sym (Int.negSuccAddSubNatNat a b (Succ c))))
  | NegSucc a, NegSucc b, OfNat c   =>
    Eq.trans (Eq.cong (t => Int.subNatNat c (Succ (Succ t))) (Nat.addComm a b))
             (Eq.sym (Int.negSuccAddSubNatNat a c (Succ b)))
  | NegSucc a, NegSucc b, NegSucc c =>
    Eq.trans (Eq.cong (t => NegSucc (Succ (Succ t))) (Nat.addAssoc a b c))
             (Eq.cong (t => NegSucc (Succ t)) (Eq.sym (Nat.addSucc a (b + c))))

theorem Nat.oneMul (n: Nat): 1 * n = n := Nat.addZero n

-- `Int` multiplication by signs and sizes: `a * b` has `a`'s size times
-- `b`'s, negated when exactly one of them is negative.
def Bool.xor: Bool -> Bool -> Bool
  | False, b => b
  | True,  b => Bool.not b

theorem Bool.xorAssoc: (a: Bool) -> (b: Bool) -> (c: Bool) -> Bool.xor (Bool.xor a b) c = Bool.xor a (Bool.xor b c)
  | False, b,     c     => rfl
  | True,  False, c     => rfl
  | True,  True,  False => rfl
  | True,  True,  True  => rfl

def Int.isNeg: Int -> Bool
  | OfNat n   => False
  | NegSucc n => True

-- `k`, negated if `neg`.
def Int.signed: Bool -> Nat -> Int
  | False, k => OfNat k
  | True,  k => Int.neg (OfNat k)

theorem Int.mulSigned: (a: Int) -> (b: Int) ->
    Int.mul a b = Int.signed (Bool.xor (Int.isNeg a) (Int.isNeg b)) (Int.natAbs a * Int.natAbs b)
  | OfNat m,   OfNat n   => rfl
  | OfNat m,   NegSucc n => rfl
  | NegSucc m, OfNat n   => rfl
  | NegSucc m, NegSucc n => rfl

theorem Int.signedMulLeft: (s: Bool) -> (k: Nat) -> (c: Int) ->
    Int.mul (Int.signed s k) c = Int.signed (Bool.xor s (Int.isNeg c)) (k * Int.natAbs c)
  | False, k,      c         => Int.mulSigned (OfNat k) c
  | True,  Zero,   OfNat n   => rfl
  | True,  Zero,   NegSucc n => rfl
  | True,  Succ j, c         => Int.mulSigned (NegSucc j) c

theorem Int.signedMulRight: (a: Int) -> (s: Bool) -> (k: Nat) ->
    Int.mul a (Int.signed s k) = Int.signed (Bool.xor (Int.isNeg a) s) (Int.natAbs a * k)
  | a,         False, k      => Int.mulSigned a (OfNat k)
  | a,         True,  Succ j => Int.mulSigned a (NegSucc j)
  | OfNat n,   True,  Zero   => rewrite Nat.mulZero n in rfl
  | NegSucc n, True,  Zero   => rewrite Nat.mulZero (Succ n) in rfl

theorem Int.mulAssoc (a: Int) (b: Int) (c: Int): Int.mul (Int.mul a b) c = Int.mul a (Int.mul b c) :=
  Eq.trans (Eq.cong (t => Int.mul t c) (Int.mulSigned a b))
    (Eq.trans (Int.signedMulLeft (Bool.xor (Int.isNeg a) (Int.isNeg b)) (Int.natAbs a * Int.natAbs b) c)
      (Eq.trans
        (Eq.trans (Eq.cong (s => Int.signed s ((Int.natAbs a * Int.natAbs b) * Int.natAbs c)) (Bool.xorAssoc (Int.isNeg a) (Int.isNeg b) (Int.isNeg c)))
          (Eq.cong (Int.signed (Bool.xor (Int.isNeg a) (Bool.xor (Int.isNeg b) (Int.isNeg c)))) (Nat.mulAssoc (Int.natAbs a) (Int.natAbs b) (Int.natAbs c))))
        (Eq.sym (Eq.trans (Eq.cong (Int.mul a) (Int.mulSigned b c))
          (Int.signedMulRight a (Bool.xor (Int.isNeg b) (Int.isNeg c)) (Int.natAbs b * Int.natAbs c))))))

theorem Int.oneMul: (a: Int) -> Int.mul (OfNat 1) a = a
  | OfNat n   => Eq.cong OfNat (Nat.addZero n)
  | NegSucc n => Eq.cong NegSucc (Nat.addZero n)

theorem Int.mulOne: (a: Int) -> Int.mul a (OfNat 1) = a
  | OfNat n   => Eq.cong OfNat (Nat.mulOne n)
  | NegSucc n => Eq.cong NegSucc (Nat.mulOne n)

-- Things you can add, starting from zero, in any order (a commutative
-- monoid): what `+` means, for every type (docs/proposals/interfaces.md
-- §6.3, §5.13).
interface Add (a: Type) =
  { zero: a
  , add: a -> a -> a
  , zeroAdd: (x: a) -> add zero x = x
  , assoc: (x: a) -> (y: a) -> (z: a) -> add (add x y) z = add x (add y z)
  , comm: (x: a) -> (y: a) -> add x y = add y x
  }

-- Things you can multiply, starting from one (a monoid; not commutative):
-- what `*` means.
interface Mul (a: Type) =
  { one: a
  , mul: a -> a -> a
  , oneMul: (x: a) -> mul one x = x
  , mulOne: (x: a) -> mul x one = x
  , assoc: (x: a) -> (y: a) -> (z: a) -> mul (mul x y) z = mul x (mul y z)
  }

-- The bootstrap phase ends here (D187): from now on `+`, `*`, `<` and `<=`
-- on `Nat` and `Int` mean these dictionaries' fields, which are the
-- operations above, so the terms are the same.
instance Nat.instAdd: Add Nat :=
  { zero = 0, add = Nat.add, zeroAdd = x => rfl, assoc = Nat.addAssoc, comm = Nat.addComm }

instance Nat.instMul: Mul Nat :=
  { one = 1, mul = Nat.mul, oneMul = Nat.oneMul, mulOne = Nat.mulOne, assoc = Nat.mulAssoc }

instance Int.instAdd: Add Int :=
  { zero = OfNat 0, add = Int.add, zeroAdd = Int.zeroAdd, assoc = Int.addAssoc, comm = Int.addComm }

instance Int.instMul: Mul Int :=
  { one = OfNat 1, mul = Int.mul, oneMul = Int.oneMul, mulOne = Int.mulOne, assoc = Int.mulAssoc }
