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
type Void : Prop

-- The proposition with exactly one proof: true.
type Unit : Prop =
  | Trivial

def Not (p : Prop) : Prop := p -> Void

-- Both propositions hold.
type And (p : Prop) (q : Prop) : Prop =
  | Both (left : p) (right : q)

-- At least one of the propositions holds: `p || q`.
type Or (p : Prop) (q : Prop) : Prop =
  | Inl (left : p)
  | Inr (right : q)

theorem And.left : [p q : Prop] -> And p q -> p
  | Both a b => a

theorem And.right : [p q : Prop] -> And p q -> q
  | Both a b => b

theorem Or.neither : [p q : Prop] -> Not p -> Not q -> Not (Or p q)
  | r, s, Inl a => r a
  | r, s, Inr b => s b

-- From a proof of `Void`, anything follows. `()` means "there's no value to
-- match here", so no right-hand side is needed.
def Void.absurd : Void -> a
  | ()

-- The same for proofs. (Without universe polymorphism, `Void.absurd`'s `a` can
-- only be a type of data.)
def Void.exfalso : [p : Prop] -> Void -> p
  | ()

-- Numbers

-- Numbers are stored compactly, but mean exactly this. `Nat.add`, `Nat.sub`, `Nat.mul`,
-- `Nat.leq`, `Nat.equal`, `Nat.divFuel`, `Nat.decEq`, `Nat.equalRefl` and `Nat.equalSound` also
-- have native implementations, used when all their arguments are numbers.
-- Each computes exactly what the definition here computes, proofs included;
-- they're tested against these definitions.
type Nat : Type =
  | Zero
  | Succ (n : Nat)

-- `a + b` means `Nat.add a b`. It recurses on its first argument, so
-- `Succ m + n` computes to `Succ (m + n)`.
def Nat.add : Nat -> Nat -> Nat
  | Zero,   n => n
  | Succ m, n => Succ (Nat.add m n)

-- `a - b`, stopping at zero: `3 - 5 = 0`.
def Nat.sub : Nat -> Nat -> Nat
  | m,      Zero   => m
  | Zero,   Succ n => Zero
  | Succ m, Succ n => Nat.sub m n

-- `a * b`
def Nat.mul : Nat -> Nat -> Nat
  | Zero,   n => 0
  | Succ m, n => n + Nat.mul m n

def Nat.pred : Nat -> Nat
  | Zero   => Zero
  | Succ n => n

-- Booleans

type Bool : Type =
  | False
  | True

def Bool.not : Bool -> Bool
  | False => True
  | True  => False

-- `if c then a else b`. The branches take a (unused) proof of `Unit` so that
-- only the chosen one is evaluated.
def Bool.ifThenElse : [a : Type] -> Bool -> (Unit -> a) -> (Unit -> a) -> a
  | True,  t, e => t Trivial
  | False, t, e => e Trivial

-- `m <= n` and `m < n` are propositions, defined by computation.
def Nat.leq : Nat -> Nat -> Bool
  | Zero,   n      => True
  | Succ m, Zero   => False
  | Succ m, Succ n => Nat.leq m n

def Nat.LessEq (m : Nat) (n : Nat) : Prop := Nat.leq m n = True

def Nat.LessThan (m : Nat) (n : Nat) : Prop := Nat.leq (Succ m) n = True

-- Lists

type List (a : Type) : Type =
  | Nil
  | Cons (head : a) (tail : List a)

-- `a` is bound automatically, as an implicit argument: `List.length : [a : Type] -> ...`.
def List.length : List a -> Nat
  | Nil       => 0
  | Cons x xs => Succ (List.length xs)

def List.append : List a -> List a -> List a
  | Nil,       ys => ys
  | Cons x xs, ys => Cons x (List.append xs ys)

-- A value that may be missing.
type Maybe (a : Type) : Type =
  | Nothing
  | Just (value : a)

-- Two values together.
type Pair (a : Type) (b : Type) : Type =
  | MkPair (fst : a) (snd : b)

def Pair.fst : Pair a b -> a
  | MkPair x y => x

def Pair.snd : Pair a b -> b
  | MkPair x y => y

-- `List.reverseOnto xs acc` is `xs` reversed, followed by `acc`.
def List.reverseOnto : List a -> List a -> List a
  | Nil,       acc => acc
  | Cons x xs, acc => List.reverseOnto xs (Cons x acc)

-- Equality lemmas, all built from `J`.

theorem Eq.cong (f : a -> b) [x y : a] (p : x = y) : f x = f y := J (\y' p' => f x = f y') rfl p

theorem Eq.sym [x y : a] (p : x = y) : y = x := J (\y' p' => y' = x) rfl p

theorem Eq.trans [x y z : a] (p : x = y) (q : y = z) : x = z := J (\z' q' => x = z') p q

-- Different constructors are different. Each proof transports along the
-- equation into a family that's `Unit` at one constructor and `Void` at the other.

def Nat.IsZero : Nat -> Prop
  | Zero   => Unit
  | Succ n => Void

theorem Nat.zeroNotSucc (n : Nat) : Not (0 = Succ n)
  | p => J (\y q => Nat.IsZero y) Trivial p

theorem Nat.succNotZero (n : Nat) : Not (Succ n = 0)
  | p => Nat.zeroNotSucc n (Eq.sym p)

theorem Nat.succInjective (m : Nat) (n : Nat) (p : Succ m = Succ n) : m = n := Eq.cong Nat.pred p

def Bool.IsFalse : Bool -> Prop
  | False => Unit
  | True  => Void

theorem Bool.falseNotTrue : Not (False = True)
  | p => J (\y q => Bool.IsFalse y) Trivial p

-- Whether two numbers are equal, as a `Bool`.
def Nat.equal : Nat -> Nat -> Bool
  | Zero,   Zero   => True
  | Zero,   Succ n => False
  | Succ m, Zero   => False
  | Succ m, Succ n => Nat.equal m n

theorem Nat.equalRefl : (n : Nat) -> Nat.equal n n = True
  | Zero   => rfl
  | Succ n => Nat.equalRefl n

-- Numbers that `Nat.equal` says are equal are equal.
theorem Nat.equalSound : (m : Nat) -> (n : Nat) -> Nat.equal m n = True -> m = n
  | Zero,   Zero,   h => rfl
  | Zero,   Succ n, h => Void.exfalso (Bool.falseNotTrue h)
  | Succ m, Zero,   h => Void.exfalso (Bool.falseNotTrue h)
  | Succ m, Succ n, h => Eq.cong Succ (Nat.equalSound m n h)

-- Numbers that `Nat.equal` says differ are different.
theorem Nat.equalFalse (m : Nat) (n : Nat) (h : Nat.equal m n = False) : Not (m = n)
  | p => Bool.falseNotTrue (Eq.trans (Eq.sym h) (J (\y q => Nat.equal m y = True) (Nat.equalRefl m) p))

-- Decisions

-- Either a proof of `p` or a proof that `p` is false. Whether it's `Yes` or
-- `No` exists at runtime; the proofs inside are erased.
type Decidable (p : Prop) : Type =
  | Yes (proof : p)
  | No (refutation : Not p)

-- `Decidable.IsYes d` is `Unit` (provable) exactly when `d` is `Yes`.
def Decidable.IsYes : Decidable p -> Prop
  | Yes h => Unit
  | No r  => Void

-- How `auto` turns a decision into a proof: `Decidable.fromYes d Trivial` only checks
-- when `d` computes to `Yes`.
def Decidable.fromYes : [p : Prop] -> (d : Decidable p) -> Decidable.IsYes d -> p
  | Yes h, u => h
  | No r,  u => Void.exfalso u

-- `a == b` is `Decidable.toBool d`, for a decision procedure `d` for `a = b`.
def Decidable.toBool : [p : Prop] -> Decidable p -> Bool
  | Yes h => True
  | No r  => False

-- `if h : p then a else b`
def Decidable.elim : [p : Prop] -> [a : Type] -> Decidable p -> (p -> a) -> (Not p -> a) -> a
  | Yes h, yes, no => yes h
  | No r,  yes, no => no r

-- Decision procedures. `auto` and `if h : …` use any function returning
-- `Decidable …`.

def Bool.decTrue : (b : Bool) -> Decidable (b = True)
  | True  => Yes rfl
  | False => No Bool.falseNotTrue

-- A decision from what `Nat.equal` says.
def Nat.decEqFrom (m : Nat) (n : Nat) : (b : Bool) -> Nat.equal m n = b -> Decidable (m = n)
  | True,  h => Yes (Nat.equalSound m n h)
  | False, h => No (Nat.equalFalse m n h)

-- For two numbers this computes `Yes rfl` or `No (Nat.equalFalse m n rfl)`, and the
-- native gives exactly that, however big they are. (Recursing on both numbers
-- one step at a time would build a refutation as deep as the smaller number.)
-- It matches on both numbers so it waits until they're known, rather than
-- unfolding around an unknown one.
def Nat.decEq : (m : Nat) -> (n : Nat) -> Decidable (m = n)
  | Zero,   Zero   => Yes rfl
  | Zero,   Succ n => No (Nat.equalFalse 0 (Succ n) rfl)
  | Succ m, Zero   => No (Nat.equalFalse (Succ m) 0 rfl)
  | Succ m, Succ n => Nat.decEqFrom (Succ m) (Succ n) (Nat.equal m n) rfl

theorem Bool.trueNotFalse : Not (True = False)
  | p => Bool.falseNotTrue (Eq.sym p)

def Bool.decEq : (a : Bool) -> (b : Bool) -> Decidable (a = b)
  | False, False => Yes rfl
  | False, True  => No Bool.falseNotTrue
  | True,  False => No Bool.trueNotFalse
  | True,  True  => Yes rfl

def Decidable.not : [p : Prop] -> Decidable p -> Decidable (Not p)
  | Yes h => No (\n => n h)
  | No r  => Yes r

-- `p && q` and `p || q` are decided from decisions of each side. Both are
-- worked out before these are called, so `if h : p && q` decides `q` even when
-- `p` is false (`if p && q`, without a name, doesn't).
def Decidable.and : [p q : Prop] -> Decidable p -> Decidable q -> Decidable (And p q)
  | Yes a, Yes b => Yes (Both a b)
  | Yes a, No r  => No (\h => r (And.right h))
  | No r,  d     => No (\h => r (And.left h))

def Decidable.or : [p q : Prop] -> Decidable p -> Decidable q -> Decidable (Or p q)
  | Yes a, d     => Yes (Inl a)
  | No r,  Yes b => Yes (Inr b)
  | No r,  No s  => No (Or.neither r s)

def Nat.decLessEq (m : Nat) (n : Nat) : Decidable (m <= n) := Bool.decTrue (Nat.leq m n)

def Nat.decLessThan (m : Nat) (n : Nat) : Decidable (m < n) := Bool.decTrue (Nat.leq (Succ m) n)

-- Proofs that two booleans are equal are unique. This is Hedberg's argument,
-- which works for any type with decidable equality: `Bool.canon` turns any proof
-- of `x = y` into one chosen by `Bool.decEq`, so it ignores which proof it was
-- given, and every proof can be recovered from its canonical one.
def Bool.canon : [x y : Bool] -> Decidable (x = y) -> x = y -> x = y
  | Yes e, p => e
  | No r,  p => Void.exfalso (r p)

theorem Bool.canonConst : [x y : Bool] -> (d : Decidable (x = y)) -> (p : x = y) -> (q : x = y) ->
    Bool.canon d p = Bool.canon d q
  | Yes e, p, q => rfl
  | No r,  p, q => Void.exfalso (r p)

theorem Bool.symThenSelf [x y : Bool] (q : x = y) : rfl = Eq.trans (Eq.sym q) q := J (\y' q' => rfl = Eq.trans (Eq.sym q') q') rfl q

theorem Bool.fromCanon (x : Bool) (y : Bool) (p : x = y) :
  p = Eq.trans (Eq.sym (Bool.canon (Bool.decEq x x) rfl)) (Bool.canon (Bool.decEq x y) p) :=
  J (\y' p' => p' = Eq.trans (Eq.sym (Bool.canon (Bool.decEq x x) rfl)) (Bool.canon (Bool.decEq x y') p'))
    (Bool.symThenSelf (Bool.canon (Bool.decEq x x) rfl)) p

theorem Bool.uniqueEq (x : Bool) (y : Bool) (p : x = y) (q : x = y) : p = q :=
  J (\z e => p = z)
    (J (\r e => p = Eq.trans (Eq.sym (Bool.canon (Bool.decEq x x) rfl)) r)
      (Bool.fromCanon x y p) (Bool.canonConst (Bool.decEq x y) p q))
    (J (\z e => z = q) rfl (Bool.fromCanon x y q))

theorem Bool.decTrueToBool : (c : Bool) -> Decidable.toBool (Bool.decTrue c) = c
  | True  => rfl
  | False => rfl

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
  J (\b' e' => (q' : Char.isScalar b' = True) -> MkChar a p = MkChar b' q')
    (\q' => J (\r e'' => MkChar a p = MkChar a r) rfl (Bool.uniqueEq (Char.isScalar a) True p q'))
    e

theorem Char.ext : (x : Char) -> (y : Char) -> Char.toNat x = Char.toNat y -> x = y
  | MkChar a p, MkChar b q, e => Char.mkExt a b p e q

def Char.decEqFrom (x : Char) (y : Char) : Decidable (Char.toNat x = Char.toNat y) -> Decidable (x = y)
  | Yes e => Yes (Char.ext x y e)
  | No r  => No (\p => r (Eq.cong Char.toNat p))

def Char.decEq (x : Char) (y : Char) : Decidable (x = y) := Char.decEqFrom x y (Nat.decEq (Char.toNat x) (Char.toNat y))

-- Division

-- Counts how many times `d` fits into `n`, using `fuel` to stay structurally
-- recursive (`n` is always enough fuel when `d` isn't zero).
def Nat.divFuel : Nat -> Nat -> Nat -> Nat
  | Zero,      n, d => 0
  | Succ fuel, n, d => if Nat.leq d n then Succ (Nat.divFuel fuel (n - d) d) else 0

-- `n / d` and `n % d` need a proof that `d` isn't zero, which `auto` finds.
def Nat.div (n : Nat) (d : Nat) : [auto ok : d != 0] -> Nat := Nat.divFuel n n d

-- The quotient goes on the left: `*` recurses on its left argument, so
-- `(n / d) * 100` stays put while checking, where `100 * (n / d)` would
-- unfold into a hundred additions.
def Nat.mod (n : Nat) (d : Nat) : [auto ok : d != 0] -> Nat := n - (n / d) * d

-- Arithmetic lemmas: addition, multiplication, order and subtraction facts proved
-- by induction, then the division law and `n % d < d`.

theorem Nat.addZero : (n : Nat) -> n + 0 = n
  | Zero => rfl
  | Succ n => Eq.cong Succ (Nat.addZero n)

theorem Nat.addSucc : (n : Nat) -> (m : Nat) -> n + Succ m = Succ (n + m)
  | Zero, m => rfl
  | Succ n, m => Eq.cong Succ (Nat.addSucc n m)

theorem Nat.addComm : (m : Nat) -> (n : Nat) -> m + n = n + m
  | Zero, n => Eq.sym (Nat.addZero n)
  | Succ m, n => Eq.trans (Eq.cong Succ (Nat.addComm m n)) (Eq.sym (Nat.addSucc n m))

theorem Nat.addAssoc : (a : Nat) -> (b : Nat) -> (c : Nat) -> (a + b) + c = a + (b + c)
  | Zero, b, c => rfl
  | Succ a, b, c => Eq.cong Succ (Nat.addAssoc a b c)

theorem Nat.addCancelLeft : (a : Nat) -> (b : Nat) -> (c : Nat) -> a + b = a + c -> b = c
  | Zero, b, c, h => h
  | Succ a, b, c, h => Nat.addCancelLeft a b c (Nat.succInjective (a + b) (a + c) h)

theorem Nat.mulZero : (n : Nat) -> n * 0 = 0
  | Zero => rfl
  | Succ n => Nat.mulZero n

theorem Nat.mulOne : (n : Nat) -> n * 1 = n
  | Zero => rfl
  | Succ n => Eq.cong Succ (Nat.mulOne n)

theorem Nat.mulSucc : (n : Nat) -> (m : Nat) -> n * Succ m = n + n * m
  | Zero, m => rfl
  | Succ n, m => Eq.cong Succ (Eq.trans (Eq.cong (\t => m + t) (Nat.mulSucc n m)) (Eq.trans (Eq.sym (Nat.addAssoc m n (n * m))) (Eq.trans (Eq.cong (\t => t + n * m) (Nat.addComm m n)) (Nat.addAssoc n m (n * m)))))

theorem Nat.mulComm : (n : Nat) -> (m : Nat) -> n * m = m * n
  | Zero, m => Eq.sym (Nat.mulZero m)
  | Succ n, m => Eq.trans (Eq.cong (\t => m + t) (Nat.mulComm n m)) (Eq.sym (Nat.mulSucc m n))

theorem Nat.mulDistribRight : (a : Nat) -> (b : Nat) -> (c : Nat) -> (a + b) * c = a * c + b * c
  | Zero, b, c => rfl
  | Succ a, b, c => Eq.trans (Eq.cong (\t => c + t) (Nat.mulDistribRight a b c)) (Eq.sym (Nat.addAssoc c (a * c) (b * c)))

theorem Nat.mulDistribLeft (a : Nat) (b : Nat) (c : Nat) : a * (b + c) = a * b + a * c := Eq.trans (Nat.mulComm a (b + c)) (Eq.trans (Nat.mulDistribRight b c a) (Eq.trans (Eq.cong (\t => t + c * a) (Nat.mulComm b a)) (Eq.cong (\t => a * b + t) (Nat.mulComm c a))))

theorem Nat.mulAssoc : (a : Nat) -> (b : Nat) -> (c : Nat) -> (a * b) * c = a * (b * c)
  | Zero, b, c => rfl
  | Succ a, b, c => Eq.trans (Nat.mulDistribRight b (a * b) c) (Eq.cong (\t => b * c + t) (Nat.mulAssoc a b c))

theorem Nat.leRefl : (n : Nat) -> n <= n
  | Zero => rfl
  | Succ n => Nat.leRefl n

theorem Nat.zeroLe (n : Nat) : 0 <= n := rfl

theorem Nat.leSucc : (n : Nat) -> n <= Succ n
  | Zero => rfl
  | Succ n => Nat.leSucc n

theorem Nat.leTrans : (a : Nat) -> (b : Nat) -> (c : Nat) -> a <= b -> b <= c -> a <= c
  | Zero, b, c, h1, h2 => rfl
  | Succ a, Zero, c, h1, h2 => Void.exfalso (Bool.falseNotTrue h1)
  | Succ a, Succ b, Zero, h1, h2 => Void.exfalso (Bool.falseNotTrue h2)
  | Succ a, Succ b, Succ c, h1, h2 => Nat.leTrans a b c h1 h2

theorem Nat.leAntisym : (a : Nat) -> (b : Nat) -> a <= b -> b <= a -> a = b
  | Zero, Zero, h1, h2 => rfl
  | Zero, Succ b, h1, h2 => Void.exfalso (Bool.falseNotTrue h2)
  | Succ a, Zero, h1, h2 => Void.exfalso (Bool.falseNotTrue h1)
  | Succ a, Succ b, h1, h2 => Eq.cong Succ (Nat.leAntisym a b h1 h2)

theorem Nat.leAddRight : (n : Nat) -> (m : Nat) -> n <= n + m
  | Zero, m => rfl
  | Succ n, m => Nat.leAddRight n m

theorem Nat.leAddLeft : (n : Nat) -> (m : Nat) -> m <= n + m
  | Zero, m => Nat.leRefl m
  | Succ n, m => Nat.leTrans m (n + m) (Succ (n + m)) (Nat.leAddLeft n m) (Nat.leSucc (n + m))

theorem Nat.leqSuccSelf : (n : Nat) -> Nat.leq (Succ n) n = False
  | Zero => rfl
  | Succ n => Nat.leqSuccSelf n

theorem Nat.lessIrrefl (n : Nat) : Not (n < n)
  | h => Bool.falseNotTrue (Eq.trans (Eq.sym (Nat.leqSuccSelf n)) h)

theorem Nat.lessLe (m : Nat) (n : Nat) (h : m < n) : m <= n := Nat.leTrans m (Succ m) n (Nat.leSucc m) h

theorem Nat.lessTrans (m : Nat) (n : Nat) (p : Nat) (h1 : m < n) (h2 : n < p) : m < p := Nat.leTrans (Succ m) n p h1 (Nat.lessLe n p h2)

theorem Nat.leLessSucc (m : Nat) (n : Nat) (h : m <= n) : m < Succ n := h

theorem Nat.subSelf : (n : Nat) -> n - n = 0
  | Zero => rfl
  | Succ n => Nat.subSelf n

theorem Nat.addSub (n : Nat) : (m : Nat) -> (n + m) - m = n
  | Zero => Nat.addZero n
  | Succ m => Eq.trans (Eq.cong (\t => t - Succ m) (Nat.addSucc n m)) (Nat.addSub n m)

theorem Nat.subLe : (n : Nat) -> (m : Nat) -> n - m <= n
  | n, Zero => Nat.leRefl n
  | Zero, Succ m => rfl
  | Succ n, Succ m => Nat.leTrans (n - m) n (Succ n) (Nat.subLe n m) (Nat.leSucc n)
theorem Nat.leCongLeft (a : Nat) (b : Nat) (n : Nat) (p : a = b) (h : a <= n) : b <= n := J (\y q => y <= n) h p

theorem Nat.leCongRight (a : Nat) (b : Nat) (n : Nat) (p : b = n) (h : a <= b) : a <= n := J (\y q => a <= y) h p

theorem Nat.ltCongLeft (a : Nat) (b : Nat) (n : Nat) (p : a = b) (h : a < n) : b < n := J (\y q => y < n) h p

theorem Nat.ltCongRight (a : Nat) (b : Nat) (n : Nat) (p : b = n) (h : a < b) : a < n := J (\y q => a < y) h p

theorem Nat.leAddCong : (d : Nat) -> (a : Nat) -> (b : Nat) -> a <= b -> d + a <= d + b
  | Zero, a, b, h => h
  | Succ d, a, b, h => Nat.leAddCong d a b h

theorem Nat.ltAddCong : (d : Nat) -> (a : Nat) -> (b : Nat) -> a < b -> d + a < d + b
  | Zero, a, b, h => h
  | Succ d, a, b, h => Nat.ltAddCong d a b h

theorem Nat.leMulRight : (a : Nat) -> (b : Nat) -> (c : Nat) -> a <= b -> a * c <= b * c
  | Zero,   b,      c, h => rfl
  | Succ a, Zero,   c, h => Void.exfalso (Bool.falseNotTrue h)
  | Succ a, Succ b, c, h => Nat.leAddCong c (a * c) (b * c) (Nat.leMulRight a b c h)

theorem Nat.leMulPos (x : Nat) : (y : Nat) -> 0 < y -> x <= x * y
  | Zero,   h => Void.exfalso (Bool.falseNotTrue h)
  | Succ y, h => Nat.leCongRight x (x + x * y) (x * Succ y) (Eq.sym (Nat.mulSucc x y)) (Nat.leAddRight x (x * y))

theorem Nat.leAddCancel : (d : Nat) -> (a : Nat) -> (b : Nat) -> d + a <= d + b -> a <= b
  | Zero,   a, b, h => h
  | Succ d, a, b, h => Nat.leAddCancel d a b h

theorem Nat.addSubCancel : (d : Nat) -> (n : Nat) -> d <= n -> d + (n - d) = n
  | Zero, n, h => rfl
  | Succ d, Zero, h => Void.exfalso (Bool.falseNotTrue h)
  | Succ d, Succ n, h => Eq.cong Succ (Nat.addSubCancel d n h)

theorem Nat.leqFalse : (d : Nat) -> (n : Nat) -> Nat.leq d n = False -> n < d
  | Zero, n, h => Void.exfalso (Bool.trueNotFalse h)
  | Succ d, Zero, h => rfl
  | Succ d, Succ n, h => Nat.leqFalse d n h

theorem Nat.subLtAdd : (n : Nat) -> (x : Nat) -> (d : Nat) -> x <= n -> n < d + x -> n - x < d
  | n, Zero, d, hx, h => Nat.ltCongRight n (d + 0) d (Nat.addZero d) h
  | Zero, Succ x, d, hx, h => Void.exfalso (Bool.falseNotTrue hx)
  | Succ n, Succ x, d, hx, h => Nat.subLtAdd n x d hx (Nat.ltCongRight (Succ n) (d + Succ x) (Succ (d + x)) (Nat.addSucc d x) h)

theorem Nat.divFuelLeStep (fuel : Nat) (n : Nat) (d : Nat) : (b : Bool) -> Nat.leq d n = b ->
    ((m : Nat) -> Nat.divFuel fuel m d * d <= m) ->
    (if b then Succ (Nat.divFuel fuel (n - d) d) else 0) * d <= n
  | True, h, ih =>
    Nat.leCongRight (d + Nat.divFuel fuel (n - d) d * d) (d + (n - d)) n (Nat.addSubCancel d n h)
      (Nat.leAddCong d (Nat.divFuel fuel (n - d) d * d) (n - d) (ih (n - d)))
  | False, h, ih => rfl

theorem Nat.divFuelLe : (fuel : Nat) -> (n : Nat) -> (d : Nat) -> Nat.divFuel fuel n d * d <= n
  | Zero, n, d => rfl
  | Succ fuel, n, d => Nat.divFuelLeStep fuel n d (Nat.leq d n) rfl (\m => Nat.divFuelLe fuel m d)

theorem Nat.fuelSub : (n : Nat) -> (d : Nat) -> (f : Nat) -> Not (d = 0) -> n <= Succ f -> n - d <= f
  | n, Zero, f, ok, h => Void.exfalso (ok rfl)
  | Zero, Succ d, f, ok, h => rfl
  | Succ n, Succ d, f, ok, h => Nat.leTrans (n - d) n f (Nat.subLe n d) h

theorem Nat.divFuelBoundStep (fuel : Nat) (n : Nat) (d : Nat) (ok : Not (d = 0)) (hn : n <= Succ fuel) : (b : Bool) -> Nat.leq d n = b ->
    ((m : Nat) -> m <= fuel -> m < Succ (Nat.divFuel fuel m d) * d) ->
    n < Succ (if b then Succ (Nat.divFuel fuel (n - d) d) else 0) * d
  | True, h, ih =>
    Nat.ltCongLeft (d + (n - d)) n (d + Succ (Nat.divFuel fuel (n - d) d) * d) (Nat.addSubCancel d n h)
      (Nat.ltAddCong d (n - d) (Succ (Nat.divFuel fuel (n - d) d) * d) (ih (n - d) (Nat.fuelSub n d fuel ok hn)))
  | False, h, ih =>
    Nat.ltCongRight n d (d + 0) (Eq.sym (Nat.addZero d)) (Nat.leqFalse d n h)

theorem Nat.nonzeroPos : (d : Nat) -> Not (d = 0) -> 0 < d
  | Zero, ok => Void.exfalso (ok rfl)
  | Succ d, ok => rfl

theorem Nat.divFuelBound : (fuel : Nat) -> (n : Nat) -> (d : Nat) -> Not (d = 0) -> n <= fuel -> n < Succ (Nat.divFuel fuel n d) * d
  | Zero, Zero, d, ok, hn => Nat.ltCongRight 0 d (d + 0) (Eq.sym (Nat.addZero d)) (Nat.nonzeroPos d ok)
  | Zero, Succ n, d, ok, hn => Void.exfalso (Bool.falseNotTrue hn)
  | Succ fuel, n, d, ok, hn => Nat.divFuelBoundStep fuel n d ok hn (Nat.leq d n) rfl (\m hm => Nat.divFuelBound fuel m d ok hm)


-- `(n / d) * d <= n`: the quotient never overshoots.
theorem Nat.divMulLe (n : Nat) (d : Nat) (ok : d != 0) : (n / d) * d <= n := Nat.divFuelLe n n d

theorem Nat.divMod (n : Nat) (d : Nat) (ok : d != 0) : n = (n / d) * d + n % d := Eq.sym (Nat.addSubCancel ((n / d) * d) n (Nat.divMulLe n d ok))

theorem Nat.modLess (n : Nat) (d : Nat) (ok : d != 0) : n % d < d := Nat.subLtAdd n ((n / d) * d) d (Nat.divMulLe n d ok) (Nat.divFuelBound n n d ok (Nat.leRefl n))

-- Division with remainder is unique: if `n = q * d + r` and `r < d`, then
-- `n / d = q` and `n % d = r`. Consequences for small numbers and for adding
-- `d`, and a few facts about subtraction.
theorem Nat.notBelowAdd (d : Nat) (r : Nat) (m : Nat) (h : r < d) (e : r = d + m) : Void := Nat.lessIrrefl r (Nat.leTrans (Succ r) d r h (Nat.leCongRight d (d + m) r (Eq.sym e) (Nat.leAddRight d m)))

theorem Nat.quotUnique (d : Nat) : (q : Nat) -> (r : Nat) -> (q2 : Nat) -> (r2 : Nat) -> r < d -> r2 < d ->
    q * d + r = q2 * d + r2 -> q = q2
  | Zero,   r, Zero,   r2, h1, h2, e => rfl
  | Zero,   r, Succ k, r2, h1, h2, e => Void.exfalso (Nat.notBelowAdd d r (k * d + r2) h1 (Eq.trans e (Nat.addAssoc d (k * d) r2)))
  | Succ a, r, Zero,   r2, h1, h2, e => Void.exfalso (Nat.notBelowAdd d r2 (a * d + r) h2 (Eq.trans (Eq.sym e) (Nat.addAssoc d (a * d) r)))
  | Succ a, r, Succ b, r2, h1, h2, e =>
    Eq.cong Succ (Nat.quotUnique d a r b r2 h1 h2
      (Nat.addCancelLeft d (a * d + r) (b * d + r2) (Eq.trans (Eq.sym (Nat.addAssoc d (a * d) r)) (Eq.trans e (Nat.addAssoc d (b * d) r2)))))

theorem Nat.divUnique (n : Nat) (d : Nat) [auto ok : d != 0] (q : Nat) (r : Nat) (h : r < d) (e : n = q * d + r) : n / d = q := Nat.quotUnique d (n / d) (n % d) q r (Nat.modLess n d ok) h (Eq.trans (Eq.sym (Nat.divMod n d ok)) e)

theorem Nat.modUnique (n : Nat) (d : Nat) [auto ok : d != 0] (q : Nat) (r : Nat) (h : r < d) (e : n = q * d + r) : n % d = r :=
  Nat.addCancelLeft (q * d) (n % d) r
    (J (\y p => y * d + n % d = q * d + r) (Eq.trans (Eq.sym (Nat.divMod n d ok)) e) (Nat.divUnique n d q r h e))

theorem Nat.modSmall (n : Nat) (d : Nat) [auto ok : d != 0] (h : n < d) : n % d = n := Nat.modUnique n d 0 n h rfl

theorem Nat.divSmall (n : Nat) (d : Nat) [auto ok : d != 0] (h : n < d) : n / d = 0 := Nat.divUnique n d 0 n h rfl

theorem Nat.addDivModSelf (d : Nat) (n : Nat) : [auto ok : d != 0] -> d + n = Succ (n / d) * d + n % d := Eq.trans (Eq.cong (\t => d + t) (Nat.divMod n d ok)) (Eq.sym (Nat.addAssoc d ((n / d) * d) (n % d)))

theorem Nat.addDivSelf (d : Nat) (n : Nat) : [auto ok : d != 0] -> (d + n) / d = Succ (n / d) := Nat.divUnique (d + n) d (Succ (n / d)) (n % d) (Nat.modLess n d ok) (Nat.addDivModSelf d n)

theorem Nat.addModSelf (d : Nat) (n : Nat) : [auto ok : d != 0] -> (d + n) % d = n % d := Nat.modUnique (d + n) d (Succ (n / d)) (n % d) (Nat.modLess n d ok) (Nat.addDivModSelf d n)

theorem Nat.zeroSub : (n : Nat) -> 0 - n = 0
  | Zero   => rfl
  | Succ n => rfl

theorem Nat.subEqZero : (n : Nat) -> (m : Nat) -> n <= m -> n - m = 0
  | Zero,   m,      h => Nat.zeroSub m
  | Succ n, Zero,   h => Void.exfalso (Bool.falseNotTrue h)
  | Succ n, Succ m, h => Nat.subEqZero n m h

theorem Nat.addOne (a : Nat) : a + 1 = Succ a := Eq.trans (Nat.addSucc a 0) (Eq.cong Succ (Nat.addZero a))

theorem Nat.modLt (n : Nat) (d : Nat) : [auto ok : d != 0] -> n % d < d := Nat.modLess n d ok

theorem Nat.modSelf (d : Nat) : [auto ok : d != 0] -> d % d = 0 := Nat.modUnique d d 1 0 (Nat.nonzeroPos d ok) (Eq.sym (Eq.trans (Nat.addZero (d + 0)) (Nat.addZero d)))

theorem Nat.divOne (n : Nat) : n / 1 = n := Nat.divUnique n 1 n 0 rfl (Eq.sym (Eq.trans (Nat.addZero (n * 1)) (Nat.mulOne n)))

theorem Nat.succAddSub : (m : Nat) -> (r : Nat) -> Succ (m + r) - m = Succ r
  | Zero,   r => rfl
  | Succ m, r => Nat.succAddSub m r

theorem Nat.subSuccRight : (j : Nat) -> (t : Nat) -> Succ j <= t -> t - j = Succ (t - Succ j)
  | j,      Zero,   h => Void.exfalso (Bool.falseNotTrue h)
  | Zero,   Succ t, h => rfl
  | Succ j, Succ t, h => Nat.subSuccRight j t h

theorem Nat.succSub : (t : Nat) -> Succ t - t = 1
  | Zero   => rfl
  | Succ t => Nat.succSub t

-- `n / d` is the largest `q` with `q * d <= n`.
theorem Nat.mulLeOfLeDiv (q : Nat) (n : Nat) (d : Nat) [auto ok : d != 0] (h : q <= n / d) : q * d <= n :=
  Nat.leTrans (q * d) ((n / d) * d) n (Nat.leMulRight q (n / d) d h) (Nat.divMulLe n d ok)

theorem Nat.leDivOfMulLe (q : Nat) (n : Nat) (d : Nat) [auto ok : d != 0] (h : q * d <= n) : q <= n / d :=
  Bool.inspect (Nat.leq q (n / d)) (\c => c = True) (\t => rfl)
    (\f => Void.exfalso (Nat.lessIrrefl n
      (Nat.leTrans (Succ n) (Succ (n / d) * d) n (Nat.divFuelBound n n d ok (Nat.leRefl n))
        (Nat.leTrans (Succ (n / d) * d) (q * d) n (Nat.leMulRight (Succ (n / d)) q d (Nat.leqFalse q (n / d) f)) h))))

theorem Nat.divLeOfLtMul (n : Nat) (b : Nat) (d : Nat) [auto ok : d != 0] (h : n < Succ b * d) : n / d <= b :=
  Bool.inspect (Nat.leq (n / d) b) (\c => c = True) (\t => rfl)
    (\f => Void.exfalso (Nat.lessIrrefl n
      (Nat.leTrans (Succ n) (Succ b * d) n h
        (Nat.leTrans (Succ b * d) ((n / d) * d) n (Nat.leMulRight (Succ b) (n / d) d (Nat.leqFalse (n / d) b f)) (Nat.divMulLe n d ok)))))

-- `(n + n) / 2 = n`
theorem Nat.halfDouble (n : Nat) : (n + n) / 2 = n :=
  Nat.divUnique (n + n) 2 n 0 rfl (Eq.sym (Eq.trans (Nat.addZero (n * 2)) (Eq.trans (Nat.mulSucc n 1) (Eq.cong (\t => n + t) (Nat.mulOne n)))))

theorem Nat.leqFalseOfLess (a : Nat) (b : Nat) (h : a < b) : Nat.leq b a = False :=
  Bool.inspect (Nat.leq b a) (\c => c = False)
    (\t => Void.exfalso (Nat.lessIrrefl a (Nat.leTrans (Succ a) b a h t)))
    (\f => rfl)


-- Lists, continued

theorem List.lengthAppend : (xs : List a) -> (ys : List a) -> List.length (List.append xs ys) = List.length xs + List.length ys
  | Nil,       ys => rfl
  | Cons x xs, ys => Eq.cong Succ (List.lengthAppend xs ys)

def List.IsNil : List a -> Prop
  | Nil       => Unit
  | Cons x xs => Void

theorem List.nilNotCons (x : a) (xs : List a) : Not (Nil = Cons x xs)
  | p => J (\y q => List.IsNil y) Trivial p

theorem List.consNotNil (x : a) (xs : List a) : Not (Cons x xs = Nil)
  | p => List.nilNotCons x xs (Eq.sym p)

def List.headOr (d : a) : List a -> a
  | Nil       => d
  | Cons x xs => x

def List.tailOf : List a -> List a
  | Nil       => Nil
  | Cons x xs => xs

def List.decCons (x : a) (y : a) (xs : List a) (ys : List a) :
    Decidable (x = y) -> Decidable (xs = ys) -> Decidable (Cons x xs = Cons y ys)
  | Yes p, Yes q => Yes (J (\y' p' => Cons x xs = Cons y' ys) (Eq.cong (Cons x) q) p)
  | No r,  dq    => No (\e => r (Eq.cong (List.headOr x) e))
  | Yes p, No r  => No (\e => r (Eq.cong List.tailOf e))

-- Equality of lists, from equality of their elements.
def List.decEq (d : (x : a) -> (y : a) -> Decidable (x = y)) : (xs : List a) -> (ys : List a) -> Decidable (xs = ys)
  | Nil,       Nil       => Yes rfl
  | Nil,       Cons y ys => No (List.nilNotCons y ys)
  | Cons x xs, Nil       => No (List.consNotNil x xs)
  | Cons x xs, Cons y ys => List.decCons x y xs ys (d x y) (List.decEq d xs ys)

def Pair.decMk (x1 : a) (x2 : a) (y1 : b) (y2 : b) :
    Decidable (x1 = x2) -> Decidable (y1 = y2) -> Decidable (MkPair x1 y1 = MkPair x2 y2)
  | Yes p, Yes q => Yes (J (\x' p' => MkPair x1 y1 = MkPair x' y2) (Eq.cong (MkPair x1) q) p)
  | No r,  dq    => No (\e => r (Eq.cong Pair.fst e))
  | Yes p, No r  => No (\e => r (Eq.cong Pair.snd e))

-- Equality of pairs, from equality of their parts.
def Pair.decEq (da : (x : a) -> (y : a) -> Decidable (x = y)) (db : (x : b) -> (y : b) -> Decidable (x = y)) :
    (p : Pair a b) -> (q : Pair a b) -> Decidable (p = q)
  | MkPair x1 y1, MkPair x2 y2 => Pair.decMk x1 x2 y1 y2 (da x1 x2) (db y1 y2)

def Maybe.IsNothing : Maybe a -> Prop
  | Nothing => Unit
  | Just x  => Void

theorem Maybe.nothingNotJust (x : a) : Not (Nothing = Just x)
  | p => J (\y q => Maybe.IsNothing y) Trivial p

theorem Maybe.justNotNothing (x : a) : Not (Just x = Nothing)
  | p => Maybe.nothingNotJust x (Eq.sym p)

-- The value, or `d` if there isn't one.
def Maybe.withDefault (d : a) : Maybe a -> a
  | Nothing => d
  | Just x  => x

def Maybe.decJust (x : a) (y : a) : Decidable (x = y) -> Decidable (Just x = Just y)
  | Yes p => Yes (Eq.cong Just p)
  | No r  => No (\e => r (Eq.cong (Maybe.withDefault x) e))

-- Equality of optional values, from equality of the values.
def Maybe.decEq (d : (x : a) -> (y : a) -> Decidable (x = y)) : (m : Maybe a) -> (n : Maybe a) -> Decidable (m = n)
  | Nothing, Nothing => Yes rfl
  | Nothing, Just y  => No (Maybe.nothingNotJust y)
  | Just x,  Nothing => No (Maybe.justNotNothing x)
  | Just x,  Just y  => Maybe.decJust x y (d x y)

-- Comparisons

type Ordering : Type =
  | Less
  | Equal
  | Greater

def Nat.compare (m : Nat) (n : Nat) : Ordering := if Nat.equal m n then Equal else (if Nat.leq m n then Less else Greater)

-- The first comparison, unless it's `Equal`.
def Ordering.andThen : Ordering -> Ordering -> Ordering
  | Less,    o => Less
  | Equal,   o => o
  | Greater, o => Greater

def Ordering.index : Ordering -> Nat
  | Less    => 0
  | Equal   => 1
  | Greater => 2

def Ordering.decEq : (a : Ordering) -> (b : Ordering) -> Decidable (a = b)
  | Less,    Less    => Yes rfl
  | Less,    Equal   => No (\p => Nat.zeroNotSucc 0 (Eq.cong Ordering.index p))
  | Less,    Greater => No (\p => Nat.zeroNotSucc 1 (Eq.cong Ordering.index p))
  | Equal,   Less    => No (\p => Nat.zeroNotSucc 0 (Eq.sym (Eq.cong Ordering.index p)))
  | Equal,   Equal   => Yes rfl
  | Equal,   Greater => No (\p => Nat.zeroNotSucc 0 (Nat.succInjective 0 1 (Eq.cong Ordering.index p)))
  | Greater, Less    => No (\p => Nat.zeroNotSucc 1 (Eq.sym (Eq.cong Ordering.index p)))
  | Greater, Equal   => No (\p => Nat.zeroNotSucc 0 (Nat.succInjective 0 1 (Eq.sym (Eq.cong Ordering.index p))))
  | Greater, Greater => Yes rfl

def Ordering.isLess : Ordering -> Bool
  | Less    => True
  | Equal   => False
  | Greater => False

-- Number helpers.
def Nat.min (m : Nat) (n : Nat) : Nat := if Nat.leq m n then m else n

def Nat.max (m : Nat) (n : Nat) : Nat := if Nat.leq m n then n else m

theorem Nat.minLeft (m : Nat) (n : Nat) (h : m <= n) : Nat.min m n = m :=
  J (\b q => Bool.ifThenElse b (\u => m) (\u => n) = m) rfl (Eq.sym h)

theorem Nat.minRight (m : Nat) (n : Nat) (h : Nat.leq m n = False) : Nat.min m n = n :=
  J (\b q => Bool.ifThenElse b (\u => m) (\u => n) = n) rfl (Eq.sym h)

-- `max` and `min` when the order is known, and their bounds.
theorem Nat.maxLeft (m : Nat) (n : Nat) (h : n <= m) : Nat.max m n = m :=
  Bool.inspect (Nat.leq m n) (\c => Bool.ifThenElse c (\u => n) (\u => m) = m) (\t => Nat.leAntisym n m h t) (\f => rfl)

theorem Nat.maxRight (m : Nat) (n : Nat) (h : m <= n) : Nat.max m n = n :=
  J (\c q => Bool.ifThenElse c (\u => n) (\u => m) = n) rfl (Eq.sym h)

theorem Nat.leMaxLeft (m : Nat) (n : Nat) : m <= Nat.max m n :=
  Bool.inspect (Nat.leq m n) (\c => m <= Bool.ifThenElse c (\u => n) (\u => m)) (\t => t) (\f => Nat.leRefl m)

theorem Nat.minLeLeft (m : Nat) (n : Nat) : Nat.min m n <= m :=
  Bool.inspect (Nat.leq m n) (\c => Bool.ifThenElse c (\u => m) (\u => n) <= m) (\t => Nat.leRefl m) (\f => Nat.lessLe n m (Nat.leqFalse m n f))

theorem Nat.minLeRight (m : Nat) (n : Nat) : Nat.min m n <= n :=
  Bool.inspect (Nat.leq m n) (\c => Bool.ifThenElse c (\u => m) (\u => n) <= n) (\t => t) (\f => Nat.leRefl n)

theorem Nat.leMin (a : Nat) (m : Nat) (n : Nat) (hm : a <= m) (hn : a <= n) : a <= Nat.min m n :=
  Bool.inspect (Nat.leq m n) (\c => a <= Bool.ifThenElse c (\u => m) (\u => n)) (\t => hm) (\f => hn)

theorem Nat.minSucc (m : Nat) (n : Nat) : Nat.min (Succ m) (Succ n) = Succ (Nat.min m n) :=
  Bool.inspect (Nat.leq m n) (\c => Bool.ifThenElse c (\u => Succ m) (\u => Succ n) = Succ (Bool.ifThenElse c (\u => m) (\u => n))) (\t => rfl) (\f => rfl)

-- The distance between two numbers; `(a - b) + (b - a)`, as one of them is 0.
def Nat.absDiff (m : Nat) (n : Nat) : Nat := (m - n) + (n - m)

-- `Nat.pow b e` is b to the power e.
def Nat.pow (b : Nat) : Nat -> Nat
  | Zero   => 1
  | Succ e => b * Nat.pow b e

-- Powers: adding exponents, positive for a positive base, growing with the
-- exponent.
theorem Nat.powAdd (b : Nat) : (e1 : Nat) -> (e2 : Nat) -> Nat.pow b (e1 + e2) = Nat.pow b e1 * Nat.pow b e2
  | Zero,    e2 => Eq.sym (Nat.addZero (Nat.pow b e2))
  | Succ e1, e2 => Eq.trans (Eq.cong (\t => b * t) (Nat.powAdd b e1 e2)) (Eq.sym (Nat.mulAssoc b (Nat.pow b e1) (Nat.pow b e2)))

theorem Nat.powSuccPos (b : Nat) : (e : Nat) -> 0 < Nat.pow (Succ b) e
  | Zero   => rfl
  | Succ e => Nat.leTrans 1 (Nat.pow (Succ b) e) (Nat.pow (Succ b) e + b * Nat.pow (Succ b) e) (Nat.powSuccPos b e) (Nat.leAddRight (Nat.pow (Succ b) e) (b * Nat.pow (Succ b) e))

theorem Nat.powMono (b : Nat) (e : Nat) (f : Nat) (h : e <= f) : Nat.pow (Succ b) e <= Nat.pow (Succ b) f :=
  Nat.leCongRight (Nat.pow (Succ b) e) (Nat.pow (Succ b) e * Nat.pow (Succ b) (f - e)) (Nat.pow (Succ b) f)
    (Eq.trans (Eq.sym (Nat.powAdd (Succ b) e (f - e))) (Eq.cong (\t => Nat.pow (Succ b) t) (Nat.addSubCancel e f h)))
    (Nat.leMulPos (Nat.pow (Succ b) e) (Nat.pow (Succ b) (f - e)) (Nat.powSuccPos b (f - e)))

-- List toolkit. The callbacks are pure: the library has no convention yet for
-- callbacks with effects or `Partial`. Every function is structurally recursive.

def List.map (f : a -> b) : List a -> List b
  | Nil       => Nil
  | Cons x xs => Cons (f x) (List.map f xs)

-- One step of `List.filter`: `x` in front of the filtered rest, or not. A
-- function of its own so the recursive call is written once: with an `if`
-- around it in both branches, a condition the checker can't decide (one on
-- a variable) keeps both branches, and the value doubles with every element.
def List.filterStep (x : a) (rest : List a) : Bool -> List a
  | True  => Cons x rest
  | False => rest

def List.filter (p : a -> Bool) : List a -> List a
  | Nil       => Nil
  | Cons x xs => List.filterStep x (List.filter p xs) (p x)

-- Left fold; tail-recursive. `List.foldLeft f z [x, y]` is `f (f z x) y`.
def List.foldLeft (f : b -> a -> b) (z : b) : List a -> b
  | Nil       => z
  | Cons x xs => List.foldLeft f (f z x) xs

-- Running accumulations, the initial value first (Haskell's `scanLeft`):
-- `List.scanLeft f z [x, y]` is `[z, f z x, f (f z x) y]`. Always one longer than
-- the input.
def List.scanLeft (f : b -> a -> b) (z : b) : List a -> List b
  | Nil       => Cons z Nil
  | Cons x xs => Cons z (List.scanLeft f (f z x) xs)

theorem List.scanLeftNil : List.scanLeft (\acc x => acc + x) 5 Nil = [5] := rfl

theorem List.scanLeftSums : List.scanLeft (\acc x => acc + x) 0 [1, 2, 3] = [0, 1, 3, 6] := rfl

-- Right fold. `List.foldRight f z [x, y]` is `f x (f y z)`.
def List.foldRight (f : a -> b -> b) (z : b) : List a -> b
  | Nil       => z
  | Cons x xs => f x (List.foldRight f z xs)

def List.sum (xs : List Nat) : Nat := List.foldLeft Nat.add 0 xs

-- The sum of `f` over the elements: `List.sumBy f xs` is `List.sum (List.map f xs)`
-- without building the intermediate list.
def List.sumBy (f : a -> Nat) (xs : List a) : Nat := List.foldLeft (\acc x => acc + f x) 0 xs

theorem List.sumByDoubles : List.sumBy (\x => x * 2) [1, 2, 3] = 12 := rfl

def List.product (xs : List Nat) : Nat := List.foldLeft Nat.mul 1 xs

def List.maximum : List Nat -> Maybe Nat
  | Nil       => Nothing
  | Cons x xs => Just (List.foldLeft Nat.max x xs)

def List.minimum : List Nat -> Maybe Nat
  | Nil       => Nothing
  | Cons x xs => Just (List.foldLeft Nat.min x xs)

-- Pairs up to the shorter list's length.
def List.zip : List a -> List b -> List (Pair a b)
  | Nil,       ys        => Nil
  | Cons x xs, Nil       => Nil
  | Cons x xs, Cons y ys => Cons (MkPair x y) (List.zip xs ys)

def List.zipWith (f : a -> b -> c) : List a -> List b -> List c
  | Nil,       ys        => Nil
  | Cons x xs, Nil       => Nil
  | Cons x xs, Cons y ys => Cons (f x y) (List.zipWith f xs ys)

-- Combines three lists up to the shortest list's length.
def List.zipWith3 (f : a -> b -> c -> d) : List a -> List b -> List c -> List d
  | Nil,       ys,        zs        => Nil
  | Cons x xs, Nil,       zs        => Nil
  | Cons x xs, Cons y ys, Nil       => Nil
  | Cons x xs, Cons y ys, Cons z zs => Cons (f x y z) (List.zipWith3 f xs ys zs)

-- The first n elements (all of them if there are fewer).
def List.take : Nat -> List a -> List a
  | Zero,   xs        => Nil
  | Succ n, Nil       => Nil
  | Succ n, Cons x xs => Cons x (List.take n xs)

-- All but the first n elements.
def List.drop : Nat -> List a -> List a
  | Zero,   xs        => xs
  | Succ n, Nil       => Nil
  | Succ n, Cons x xs => List.drop n xs

-- The element at index i, counting from 0.
def List.get : Nat -> List a -> Maybe a
  | i,      Nil       => Nothing
  | Zero,   Cons x xs => Just x
  | Succ i, Cons x xs => List.get i xs

def List.any (p : a -> Bool) : List a -> Bool
  | Nil       => False
  | Cons x xs => if p x then True else List.any p xs

def List.all (p : a -> Bool) : List a -> Bool
  | Nil       => True
  | Cons x xs => if p x then List.all p xs else False

-- `n`, plus one if `b`: `List.count`'s step. A function of its own so `n` is
-- written once: `if b then Succ n else n` writes it twice, so when the
-- checker can't decide the conditions, a count doubles in size with every
-- element.
def Nat.succIf (n : Nat) : Bool -> Nat
  | True  => Succ n
  | False => n

-- How many elements satisfy `p`.
def List.count (p : a -> Bool) (xs : List a) : Nat := List.foldLeft (\n x => Nat.succIf n (p x)) 0 xs

-- The first element satisfying `p`.
def List.find (p : a -> Bool) : List a -> Maybe a
  | Nil       => Nothing
  | Cons x xs => if p x then Just x else List.find p xs

def List.consJust : Maybe b -> List b -> List b
  | Nothing, rest => rest
  | Just y,  rest => Cons y rest

-- Keeps the `Just` results, in order.
def List.mapMaybe (f : a -> Maybe b) : List a -> List b
  | Nil       => Nil
  | Cons x xs => List.consJust (f x) (List.mapMaybe f xs)

-- Joins a list of lists.
def List.concat : List (List a) -> List a
  | Nil         => Nil
  | Cons xs xss => List.append xs (List.concat xss)

def List.concatMap (f : a -> List b) : List a -> List b
  | Nil       => Nil
  | Cons x xs => List.append (f x) (List.concatMap f xs)

-- `List.replicate n x` is n copies of x.
def List.replicate : Nat -> a -> List a
  | Zero,   x => Nil
  | Succ n, x => Cons x (List.replicate n x)

def List.rangeFrom : Nat -> Nat -> List Nat
  | Zero,   i => Nil
  | Succ n, i => Cons i (List.rangeFrom n (Succ i))

-- `List.range n` is `[0, 1, ..., n - 1]`.
def List.range (n : Nat) : List Nat := List.rangeFrom n 0

def List.reverse (xs : List a) : List a := List.reverseOnto xs Nil

def List.last : List a -> Maybe a
  | Nil                => Nothing
  | Cons x Nil         => Just x
  | Cons x (Cons y ys) => List.last (Cons y ys)

-- Membership, given a decision for equality (as `List.decEq` takes).
def List.elem (d : (x : a) -> (y : a) -> Decidable (x = y)) (z : a) : List a -> Bool
  | Nil       => False
  | Cons x xs => if Decidable.toBool (d z x) then True else List.elem d z xs

-- The elements that satisfy `p`, and those that don't.
def List.partition (p : a -> Bool) (xs : List a) : Pair (List a) (List a) := MkPair (List.filter p xs) (List.filter (\x => Bool.not (p x)) xs)

-- The value for the first pair whose key is equal, given a decision for equality.
def List.lookup (d : (x : k) -> (y : k) -> Decidable (x = y)) (key : k) : List (Pair k v) -> Maybe v
  | Nil                    => Nothing
  | Cons (MkPair k v) rest => if Decidable.toBool (d key k) then Just v else List.lookup d key rest

-- Sorting

-- `Bool.inspect b motive t f` proves `motive b` by cases on `b`, remembering
-- which case it is. A proof about `if le x y then ... else ...` uses it with
-- `b = le x y` to get the branch's evidence (`le x y = True` or `= False`).
theorem Bool.inspect : (b : Bool) -> (motive : Bool -> Prop) -> (b = True -> motive True) -> (b = False -> motive False) -> motive b
  | True,  m, t, f => t rfl
  | False, m, t, f => f rfl

-- 1 for `True`, 0 for `False`.
def Bool.toNat : Bool -> Nat
  | False => 0
  | True  => 1

theorem Nat.addRotate (a : Nat) (b : Nat) (c : Nat) : (a + b) + c = b + (a + c) := Eq.trans (Eq.cong (\t => t + c) (Nat.addComm a b)) (Nat.addAssoc b a c)

theorem Nat.addLeftComm (a : Nat) (b : Nat) (c : Nat) : a + (b + c) = b + (a + c) := Eq.trans (Eq.sym (Nat.addAssoc a b c)) (Nat.addRotate a b c)

-- `<=` is total: if `m <= n` is false, then `n <= m`.
theorem Nat.leqTotal (m : Nat) (n : Nat) (h : Nat.leq m n = False) : Nat.leq n m = True := Nat.lessLe n m (Nat.leqFalse m n h)

-- Sums of lists: one element at a time, sums of intervals (Gauss), and
-- rewriting under `map`, `filter` and `foldLeft`.
theorem Nat.addSwap (a : Nat) (b : Nat) (c : Nat) (d : Nat) : (a + b) + (c + d) = (a + c) + (b + d) :=
  Eq.trans (Nat.addAssoc a b (c + d))
    (Eq.trans (Eq.cong (\t => a + t) (Nat.addLeftComm b c d)) (Eq.sym (Nat.addAssoc a c (b + d))))

theorem List.sumFrom : (a : Nat) -> (xs : List Nat) -> List.foldLeft Nat.add a xs = a + List.sum xs
  | a, Nil       => Eq.sym (Nat.addZero a)
  | a, Cons x xs =>
    Eq.trans (List.sumFrom (a + x) xs)
      (Eq.trans (Nat.addAssoc a x (List.sum xs)) (Eq.cong (\t => a + t) (Eq.sym (List.sumFrom x xs))))

theorem List.sumCons (x : Nat) (xs : List Nat) : List.sum (Cons x xs) = x + List.sum xs := List.sumFrom x xs

theorem List.sumByFrom (f : a -> Nat) : (z : Nat) -> (xs : List a) -> List.foldLeft (\acc x => acc + f x) z xs = z + List.sumBy f xs
  | z, Nil       => Eq.sym (Nat.addZero z)
  | z, Cons x xs =>
    Eq.trans (List.sumByFrom f (z + f x) xs)
      (Eq.trans (Nat.addAssoc z (f x) (List.sumBy f xs)) (Eq.cong (\t => z + t) (Eq.sym (List.sumByFrom f (f x) xs))))

theorem List.sumByCons (f : a -> Nat) (x : a) (xs : List a) : List.sumBy f (Cons x xs) = f x + List.sumBy f xs := List.sumByFrom f (f x) xs

theorem List.sumByCongr (f : a -> Nat) (g : a -> Nat) (h : (x : a) -> f x = g x) : (xs : List a) -> List.sumBy f xs = List.sumBy g xs
  | Nil       => rfl
  | Cons x xs =>
    Eq.trans (List.sumByCons f x xs)
      (Eq.trans (Eq.cong (\t => t + List.sumBy f xs) (h x))
        (Eq.trans (Eq.cong (\t => g x + t) (List.sumByCongr f g h xs)) (Eq.sym (List.sumByCons g x xs))))

theorem List.sumByMulLeft (c : Nat) (f : a -> Nat) : (xs : List a) -> List.sumBy (\x => c * f x) xs = c * List.sumBy f xs
  | Nil       => Eq.sym (Nat.mulZero c)
  | Cons x xs =>
    Eq.trans (List.sumByCons (\y => c * f y) x xs)
      (Eq.trans (Eq.cong (\t => c * f x + t) (List.sumByMulLeft c f xs))
        (Eq.sym (Eq.trans (Eq.cong (\t => c * t) (List.sumByCons f x xs)) (Nat.mulDistribLeft c (f x) (List.sumBy f xs)))))

theorem List.sumByRangeShift (f : Nat -> Nat) : (n : Nat) -> (s : Nat) ->
    List.sumBy f (List.rangeFrom n (Succ s)) = List.sumBy (\i => f (Succ i)) (List.rangeFrom n s)
  | Zero,   s => rfl
  | Succ n, s =>
    Eq.trans (List.sumByCons f (Succ s) (List.rangeFrom n (Succ (Succ s))))
      (Eq.trans (Eq.cong (\t => f (Succ s) + t) (List.sumByRangeShift f n (Succ s)))
        (Eq.sym (List.sumByCons (\i => f (Succ i)) s (List.rangeFrom n (Succ s)))))

-- Gauss: twice the sum of `x, x + 1, ..., x + d` is `(d + 1) * (x + (x + d))`.
theorem List.gaussSum : (d : Nat) -> (x : Nat) ->
    List.sum (List.rangeFrom (Succ d) x) + List.sum (List.rangeFrom (Succ d) x) = Succ d * (x + (x + d))
  | Zero,   x => Eq.sym (Eq.trans (Nat.addZero (x + (x + 0))) (Eq.cong (\t => x + t) (Nat.addZero x)))
  | Succ d, x =>
    Eq.trans (Eq.cong (\t => t + t) (List.sumCons x (List.rangeFrom (Succ d) (Succ x))))
      (Eq.trans (Nat.addSwap x (List.sum (List.rangeFrom (Succ d) (Succ x))) x (List.sum (List.rangeFrom (Succ d) (Succ x))))
        (Eq.trans (Eq.cong (\t => (x + x) + t) (List.gaussSum d (Succ x)))
          (Eq.trans (Eq.cong (\t => (x + x) + Succ d * Succ (x + t)) (Eq.sym (Nat.addSucc x d)))
            (Eq.trans (Eq.cong (\t => (x + x) + t) (Nat.mulSucc (Succ d) (x + (x + Succ d))))
              (Eq.trans (Eq.sym (Nat.addAssoc (x + x) (Succ d) (Succ d * (x + (x + Succ d)))))
                (Eq.cong (\t => t + Succ d * (x + (x + Succ d))) (Nat.addAssoc x x (Succ d))))))))

theorem List.mapCongr (f : a -> b) (g : a -> b) (h : (x : a) -> f x = g x) : (xs : List a) -> List.map f xs = List.map g xs
  | Nil       => rfl
  | Cons x xs => Eq.trans (Eq.cong (\y => Cons y (List.map f xs)) (h x)) (Eq.cong (\ys => Cons (g x) ys) (List.mapCongr f g h xs))

theorem List.filterKeep (p : a -> Bool) (x : a) (xs : List a) (h : p x = True) : List.filter p (Cons x xs) = Cons x (List.filter p xs) :=
  J (\c q => List.filterStep x (List.filter p xs) c = Cons x (List.filter p xs)) rfl (Eq.sym h)

theorem List.filterSkip (p : a -> Bool) (x : a) (xs : List a) (h : p x = False) : List.filter p (Cons x xs) = List.filter p xs :=
  J (\c q => List.filterStep x (List.filter p xs) c = List.filter p xs) rfl (Eq.sym h)

theorem List.foldLeftAppend (f : b -> a -> b) : (z : b) -> (xs : List a) -> (ys : List a) ->
    List.foldLeft f z (List.append xs ys) = List.foldLeft f (List.foldLeft f z xs) ys
  | z, Nil,       ys => rfl
  | z, Cons x xs, ys => List.foldLeftAppend f (f z x) xs ys

-- `True` for `Less` and `Equal`.
def Ordering.isLessEq : Ordering -> Bool
  | Less    => True
  | Equal   => True
  | Greater => False

theorem Ordering.isLessEqIf : (d : Bool) -> Ordering.isLessEq (if d then Less else Greater) = d
  | True  => rfl
  | False => rfl

-- `Nat.compare` agrees with `<=`, so `List.sortBy` with it is total.
theorem Nat.compareLeq (m : Nat) (n : Nat) : Ordering.isLessEq (Nat.compare m n) = Nat.leq m n :=
  Bool.inspect (Nat.equal m n)
    (\c => Ordering.isLessEq (if c then Equal else (if Nat.leq m n then Less else Greater)) = Nat.leq m n)
    (\e => Eq.sym (Nat.leCongRight m m n (Nat.equalSound m n e) (Nat.leRefl m)))
    (\e => Ordering.isLessEqIf (Nat.leq m n))

theorem Nat.compareTotal (m : Nat) (n : Nat)
  (h : Ordering.isLessEq (Nat.compare m n) = False) : Ordering.isLessEq (Nat.compare n m) = True := Eq.trans (Nat.compareLeq n m) (Nat.leqTotal m n (Eq.trans (Eq.sym (Nat.compareLeq m n)) h))

-- Merges two lists sorted by `le` ("may come before"), taking from the first
-- list on ties.
def List.merge (le : a -> a -> Bool) : List a -> List a -> List a
  | Nil,       ys        => ys
  | Cons x xs, Nil       => Cons x xs
  | Cons x xs, Cons y ys =>
    if le x y then Cons x (List.merge le xs (Cons y ys)) else Cons y (List.merge le (Cons x xs) ys)

-- Bottom-up merge sort, structurally recursive throughout. The runs are kept
-- like the digits of a binary counter: slot `i` is empty or holds a sorted run
-- of 2^i elements, newest first. Adding an element carries: two runs of the
-- same size merge into the next slot. Each element takes part in about log n
-- merges, so sorting is O(n log n).
def List.pushRun (le : a -> a -> Bool) (run : List a) : List (Maybe (List a)) -> List (Maybe (List a))
  | Nil                => Cons (Just run) Nil
  | Cons Nothing rest  => Cons (Just run) rest
  | Cons (Just r) rest => Cons Nothing (List.pushRun le (List.merge le r run) rest)

def List.buildRuns (le : a -> a -> Bool) (c : List (Maybe (List a))) : List a -> List (Maybe (List a))
  | Nil       => c
  | Cons x xs => List.buildRuns le (List.pushRun le (Cons x Nil) c) xs

-- Merges the runs, older (earlier) ones on the left.
def List.mergeRuns (le : a -> a -> Bool) (acc : List a) : List (Maybe (List a)) -> List a
  | Nil                => acc
  | Cons Nothing rest  => List.mergeRuns le acc rest
  | Cons (Just r) rest => List.mergeRuns le (List.merge le r acc) rest

-- Sorts by `le`, which says whether its first argument may come before its
-- second (`Nat.leq` for ascending numbers). Stable: equal elements keep their
-- order. `List.sortWithSorted` and `List.sortWithPerm` say it's correct.
def List.sortWith (le : a -> a -> Bool) (xs : List a) : List a := List.mergeRuns le Nil (List.buildRuns le Nil xs)

-- Sorts by a comparison, such as `Nat.compare` or `Text.compare`.
def List.sortBy (cmp : a -> a -> Ordering) (xs : List a) : List a := List.sortWith (\x y => Ordering.isLessEq (cmp x y)) xs

-- Sorts numbers into ascending order.
def List.sort (xs : List Nat) : List Nat := List.sortWith Nat.leq xs

-- `List.LeHead le z xs`: `z` may come before the first element of `xs`, if any.
def List.LeHead (le : a -> a -> Bool) (z : a) : List a -> Prop
  | Nil       => Unit
  | Cons y ys => le z y = True

-- Each element may come before the next. For a transitive `le`, such as
-- `Nat.leq`, that orders every pair.
def List.Sorted (le : a -> a -> Bool) : List a -> Prop
  | Nil       => Unit
  | Cons x xs => And (List.LeHead le x xs) (List.Sorted le xs)

-- The correctness proofs need only that `le` is total: `tot` below.
theorem List.mergeLeHead (le : a -> a -> Bool) (z : a) : (xs : List a) -> (ys : List a) ->
    List.LeHead le z xs -> List.LeHead le z ys -> List.LeHead le z (List.merge le xs ys)
  | Nil,       ys,        hx, hy => hy
  | Cons x xs, Nil,       hx, hy => hx
  | Cons x xs, Cons y ys, hx, hy =>
    Bool.inspect (le x y)
      (\c => List.LeHead le z (if c then Cons x (List.merge le xs (Cons y ys)) else Cons y (List.merge le (Cons x xs) ys)))
      (\e => hx) (\e => hy)

theorem List.mergeSorted (le : a -> a -> Bool) (tot : (x : a) -> (y : a) -> le x y = False -> le y x = True) :
    (xs : List a) -> (ys : List a) -> List.Sorted le xs -> List.Sorted le ys -> List.Sorted le (List.merge le xs ys)
  | Nil,       ys,        sx, sy => sy
  | Cons x xs, Nil,       sx, sy => sx
  | Cons x xs, Cons y ys, Both hx sxs, Both hy sys =>
    Bool.inspect (le x y)
      (\c => List.Sorted le (if c then Cons x (List.merge le xs (Cons y ys)) else Cons y (List.merge le (Cons x xs) ys)))
      (\e => Both (List.mergeLeHead le x xs (Cons y ys) hx e) (List.mergeSorted le tot xs (Cons y ys) sxs (Both hy sys)))
      (\e => Both (List.mergeLeHead le y (Cons x xs) ys (tot x y e) hy) (List.mergeSorted le tot (Cons x xs) ys (Both hx sxs) sys))

-- Every run in the counter is sorted.
def List.RunsSorted (le : a -> a -> Bool) : List (Maybe (List a)) -> Prop
  | Nil                => Unit
  | Cons Nothing rest  => List.RunsSorted le rest
  | Cons (Just r) rest => And (List.Sorted le r) (List.RunsSorted le rest)

theorem List.pushRunSorted (le : a -> a -> Bool) (tot : (x : a) -> (y : a) -> le x y = False -> le y x = True)
    (run : List a) : (c : List (Maybe (List a))) -> List.Sorted le run -> List.RunsSorted le c -> List.RunsSorted le (List.pushRun le run c)
  | Nil,                s, h         => Both s Trivial
  | Cons Nothing rest,  s, h         => Both s h
  | Cons (Just r) rest, s, Both sr h =>
    List.pushRunSorted le tot (List.merge le r run) rest (List.mergeSorted le tot r run sr s) h

theorem List.buildRunsSorted (le : a -> a -> Bool) (tot : (x : a) -> (y : a) -> le x y = False -> le y x = True)
    (c : List (Maybe (List a))) : (xs : List a) -> List.RunsSorted le c -> List.RunsSorted le (List.buildRuns le c xs)
  | Nil,       h => h
  | Cons x xs, h =>
    List.buildRunsSorted le tot (List.pushRun le (Cons x Nil) c) xs (List.pushRunSorted le tot (Cons x Nil) c (Both Trivial Trivial) h)

theorem List.mergeRunsSorted (le : a -> a -> Bool) (tot : (x : a) -> (y : a) -> le x y = False -> le y x = True)
    (acc : List a) : (c : List (Maybe (List a))) -> List.Sorted le acc -> List.RunsSorted le c -> List.Sorted le (List.mergeRuns le acc c)
  | Nil,                s, h         => s
  | Cons Nothing rest,  s, h         => List.mergeRunsSorted le tot acc rest s h
  | Cons (Just r) rest, s, Both sr h =>
    List.mergeRunsSorted le tot (List.merge le r acc) rest (List.mergeSorted le tot r acc sr s) h

theorem List.sortWithSorted (le : a -> a -> Bool) (tot : (x : a) -> (y : a) -> le x y = False -> le y x = True)
  (xs : List a) : List.Sorted le (List.sortWith le xs) :=
  List.mergeRunsSorted le tot Nil (List.buildRuns le Nil xs) Trivial (List.buildRunsSorted le tot Nil xs Trivial)

theorem List.sortBySorted (cmp : a -> a -> Ordering)
  (tot : (x : a) -> (y : a) -> Ordering.isLessEq (cmp x y) = False -> Ordering.isLessEq (cmp y x) = True)
  (xs : List a) : List.Sorted (\x y => Ordering.isLessEq (cmp x y)) (List.sortBy cmp xs) := List.sortWithSorted (\x y => Ordering.isLessEq (cmp x y)) tot xs

theorem List.sortSorted (xs : List Nat) : List.Sorted Nat.leq (List.sort xs) := List.sortWithSorted Nat.leq Nat.leqTotal xs

-- How many elements satisfy `p` (as `List.count`, but recursing on the list,
-- which suits proofs).
def List.occurrences (p : a -> Bool) : List a -> Nat
  | Nil       => 0
  | Cons x xs => Bool.toNat (p x) + List.occurrences p xs

-- `List.count` is `List.occurrences`, which suits proofs; counting and
-- `List.scanLeft` over `++`. (`List.drop 1` drops the starting value.)
theorem List.countStep : (b : Bool) -> (k : Nat) -> (o : Nat) -> Nat.succIf k b + o = k + (Bool.toNat b + o)
  | True,  k, o => Eq.sym (Nat.addSucc k o)
  | False, k, o => rfl

theorem List.countFold (p : a -> Bool) (k : Nat) : (xs : List a) ->
    List.foldLeft (\n x => Nat.succIf n (p x)) k xs = k + List.occurrences p xs
  | Nil       => Eq.sym (Nat.addZero k)
  | Cons x xs => Eq.trans (List.countFold p (Nat.succIf k (p x)) xs) (List.countStep (p x) k (List.occurrences p xs))

theorem List.countOccurrences (p : a -> Bool) (xs : List a) : List.count p xs = List.occurrences p xs := List.countFold p 0 xs

theorem List.occurrencesAppend (p : a -> Bool) : (xs : List a) -> (ys : List a) ->
    List.occurrences p (List.append xs ys) = List.occurrences p xs + List.occurrences p ys
  | Nil,       ys => rfl
  | Cons x xs, ys =>
    Eq.trans (Eq.cong (\t => Bool.toNat (p x) + t) (List.occurrencesAppend p xs ys))
      (Eq.sym (Nat.addAssoc (Bool.toNat (p x)) (List.occurrences p xs) (List.occurrences p ys)))

theorem List.scanLeftCons (f : b -> a -> b) (z : b) : (xs : List a) -> List.scanLeft f z xs = Cons z (List.drop 1 (List.scanLeft f z xs))
  | Nil       => rfl
  | Cons x xs => rfl

theorem List.scanLeftAppend (f : b -> a -> b) (z : b) : (xs : List a) -> (ys : List a) ->
    List.drop 1 (List.scanLeft f z (List.append xs ys)) = List.append (List.drop 1 (List.scanLeft f z xs)) (List.drop 1 (List.scanLeft f (List.foldLeft f z xs) ys))
  | Nil,       ys => rfl
  | Cons x xs, ys =>
    Eq.trans (List.scanLeftCons f (f z x) (List.append xs ys))
      (Eq.trans (Eq.cong (Cons (f z x)) (List.scanLeftAppend f (f z x) xs ys))
        (Eq.cong (\l => List.append l (List.drop 1 (List.scanLeft f (List.foldLeft f (f z x) xs) ys))) (Eq.sym (List.scanLeftCons f (f z x) xs))))


-- `xs` and `ys` are permutations of each other: every test is passed by as
-- many elements of one as of the other. For elements with decidable equality
-- this is the usual meaning (test with `Nat.equal v` for each `v`). Counting
-- turns the proofs into arithmetic, and needs no equality on the elements.
def List.Perm (xs : List a) (ys : List a) : Prop := (p : a -> Bool) -> List.occurrences p xs = List.occurrences p ys

theorem List.permRefl (xs : List a) : List.Perm xs xs := \p => rfl

theorem List.permSym (xs : List a) (ys : List a) (h : List.Perm xs ys) : List.Perm ys xs := \p => Eq.sym (h p)

theorem List.permTrans (xs : List a) (ys : List a) (zs : List a) (h1 : List.Perm xs ys) (h2 : List.Perm ys zs) : List.Perm xs zs := \p => Eq.trans (h1 p) (h2 p)

theorem List.occurrencesTrue : (xs : List a) -> List.occurrences (\x => True) xs = List.length xs
  | Nil       => rfl
  | Cons x xs => Eq.cong Succ (List.occurrencesTrue xs)

theorem List.permLength (xs : List a) (ys : List a) (h : List.Perm xs ys) : List.length xs = List.length ys := Eq.trans (Eq.sym (List.occurrencesTrue xs)) (Eq.trans (h (\x => True)) (List.occurrencesTrue ys))

-- `s` is `xs` with some elements left out, the rest kept in order: each
-- element of `s` is matched with an element of `xs`, or `xs`'s first element
-- is skipped.
def List.Subsequence : List a -> List a -> Prop
  | Nil,       ys        => Unit
  | Cons x xs, Nil       => Void
  | Cons x xs, Cons y ys => Or (And (x = y) (List.Subsequence xs ys)) (List.Subsequence (Cons x xs) ys)

-- Adding an element in front keeps every subsequence.
theorem List.subsequenceCons (x : a) : (s : List a) -> (ys : List a) -> List.Subsequence s ys -> List.Subsequence s (Cons x ys)
  | Nil,      ys, h => Trivial
  | Cons y s, ys, h => Inr h

theorem List.subsequenceRefl : (xs : List a) -> List.Subsequence xs xs
  | Nil       => Trivial
  | Cons x xs => Inl (Both rfl (List.subsequenceRefl xs))

theorem List.subsequenceLength : (s : List a) -> (ys : List a) -> List.Subsequence s ys -> List.length s <= List.length ys
  | Nil,       ys,        h              => rfl
  | Cons x xs, Nil,       h              => Void.exfalso h
  | Cons x xs, Cons y ys, Inl (Both e h) => List.subsequenceLength xs ys h
  | Cons x xs, Cons y ys, Inr h          =>
    Nat.leTrans (List.length (Cons x xs)) (List.length ys) (Succ (List.length ys)) (List.subsequenceLength (Cons x xs) ys h) (Nat.leSucc (List.length ys))

theorem List.mergeCount (le : a -> a -> Bool) (p : a -> Bool) : (xs : List a) -> (ys : List a) ->
    List.occurrences p (List.merge le xs ys) = List.occurrences p xs + List.occurrences p ys
  | Nil,       ys        => rfl
  | Cons x xs, Nil       => Eq.sym (Nat.addZero (List.occurrences p (Cons x xs)))
  | Cons x xs, Cons y ys =>
    Bool.inspect (le x y)
      (\c => List.occurrences p (if c then Cons x (List.merge le xs (Cons y ys)) else Cons y (List.merge le (Cons x xs) ys))
        = List.occurrences p (Cons x xs) + List.occurrences p (Cons y ys))
      (\e => Eq.trans (Eq.cong (\t => Bool.toNat (p x) + t) (List.mergeCount le p xs (Cons y ys)))
        (Eq.sym (Nat.addAssoc (Bool.toNat (p x)) (List.occurrences p xs) (List.occurrences p (Cons y ys)))))
      (\e => Eq.trans (Eq.cong (\t => Bool.toNat (p y) + t) (List.mergeCount le p (Cons x xs) ys))
        (Nat.addLeftComm (Bool.toNat (p y)) (List.occurrences p (Cons x xs)) (List.occurrences p ys)))

-- How many elements of all the runs satisfy `p`.
def List.runsCount (p : a -> Bool) : List (Maybe (List a)) -> Nat
  | Nil                => 0
  | Cons Nothing rest  => List.runsCount p rest
  | Cons (Just r) rest => List.occurrences p r + List.runsCount p rest

theorem List.pushRunCount (le : a -> a -> Bool) (p : a -> Bool) (run : List a) : (c : List (Maybe (List a))) ->
    List.runsCount p (List.pushRun le run c) = List.occurrences p run + List.runsCount p c
  | Nil                => rfl
  | Cons Nothing rest  => rfl
  | Cons (Just r) rest =>
    Eq.trans (List.pushRunCount le p (List.merge le r run) rest)
      (Eq.trans (Eq.cong (\t => t + List.runsCount p rest) (List.mergeCount le p r run))
        (Nat.addRotate (List.occurrences p r) (List.occurrences p run) (List.runsCount p rest)))

theorem List.buildRunsCount (le : a -> a -> Bool) (p : a -> Bool) (c : List (Maybe (List a))) : (xs : List a) ->
    List.runsCount p (List.buildRuns le c xs) = List.runsCount p c + List.occurrences p xs
  | Nil       => Eq.sym (Nat.addZero (List.runsCount p c))
  | Cons x xs =>
    Eq.trans (List.buildRunsCount le p (List.pushRun le (Cons x Nil) c) xs)
      (Eq.trans (Eq.cong (\t => t + List.occurrences p xs) (List.pushRunCount le p (Cons x Nil) c))
        (Eq.trans (Eq.cong (\t => (t + List.runsCount p c) + List.occurrences p xs) (Nat.addZero (Bool.toNat (p x))))
          (Nat.addRotate (Bool.toNat (p x)) (List.runsCount p c) (List.occurrences p xs))))

theorem List.mergeRunsCount (le : a -> a -> Bool) (p : a -> Bool) (acc : List a) : (c : List (Maybe (List a))) ->
    List.occurrences p (List.mergeRuns le acc c) = List.occurrences p acc + List.runsCount p c
  | Nil                => Eq.sym (Nat.addZero (List.occurrences p acc))
  | Cons Nothing rest  => List.mergeRunsCount le p acc rest
  | Cons (Just r) rest =>
    Eq.trans (List.mergeRunsCount le p (List.merge le r acc) rest)
      (Eq.trans (Eq.cong (\t => t + List.runsCount p rest) (List.mergeCount le p r acc))
        (Nat.addRotate (List.occurrences p r) (List.occurrences p acc) (List.runsCount p rest)))

theorem List.sortWithPerm (le : a -> a -> Bool) (xs : List a) : List.Perm (List.sortWith le xs) xs := \p =>
  Eq.trans (List.mergeRunsCount le p Nil (List.buildRuns le Nil xs)) (List.buildRunsCount le p Nil xs)

theorem List.sortByPerm (cmp : a -> a -> Ordering) (xs : List a) : List.Perm (List.sortBy cmp xs) xs := List.sortWithPerm (\x y => Ordering.isLessEq (cmp x y)) xs

theorem List.sortPerm (xs : List Nat) : List.Perm (List.sort xs) xs := List.sortWithPerm Nat.leq xs

theorem List.sortLength (xs : List Nat) : List.length (List.sort xs) = List.length xs := List.permLength (List.sort xs) xs (List.sortPerm xs)

-- Text (docs/proposals/text-and-io.md)

-- A sequence of Unicode scalar values. `"héllo"` is a `Text`. Equality and
-- ordering compare the sequence exactly, by scalar value, and length counts
-- scalar values; nothing is normalised, so `"\u{E9}"` and `"e\u{301}"` are
-- different texts. Code that goes through `Text.toList` and `Text.fromList`
-- and their lemmas, rather than `MkText`, won't depend on the representation.
type Text : Type =
  | MkText (chars : List Char)

def Text.toList : Text -> List Char
  | MkText cs => cs

def Text.fromList (cs : List Char) : Text := MkText cs

theorem Text.toFromList (cs : List Char) : Text.toList (Text.fromList cs) = cs := rfl

theorem Text.fromToList : (t : Text) -> Text.fromList (Text.toList t) = t
  | MkText cs => rfl

-- `a ++ b`
def Text.append (a : Text) (b : Text) : Text := MkText (List.append (Text.toList a) (Text.toList b))

-- The number of scalar values.
def Text.length (t : Text) : Nat := List.length (Text.toList t)

theorem Text.lengthAppend (a : Text) (b : Text) :
  Text.length (Text.append a b) = Text.length a + Text.length b := List.lengthAppend (Text.toList a) (Text.toList b)

def Text.isEmpty : Text -> Bool
  | MkText Nil         => True
  | MkText (Cons c cs) => False

def Text.decEqFrom (a : Text) (b : Text) : Decidable (Text.toList a = Text.toList b) -> Decidable (a = b)
  | Yes p => Yes (Eq.trans (Eq.sym (Text.fromToList a)) (Eq.trans (Eq.cong Text.fromList p) (Text.fromToList b)))
  | No r  => No (\p => r (Eq.cong Text.toList p))

def Text.decEq (a : Text) (b : Text) : Decidable (a = b) := Text.decEqFrom a b (List.decEq Char.decEq (Text.toList a) (Text.toList b))

-- The first character and the rest, unless the text is empty.
def Text.uncons : Text -> Maybe (Pair Char Text)
  | MkText Nil         => Nothing
  | MkText (Cons c cs) => Just (MkPair c (MkText cs))

def Text.foldChars (f : Char -> b -> b) (z : b) : List Char -> b
  | Nil       => z
  | Cons c cs => f c (Text.foldChars f z cs)

-- `Text.fold f z "abc"` is `f 'a' (f 'b' (f 'c' z))`.
def Text.fold (f : Char -> b -> b) (z : b) (t : Text) : b := Text.foldChars f z (Text.toList t)

def Text.compareChars : List Char -> List Char -> Ordering
  | Nil,       Nil       => Equal
  | Nil,       Cons y ys => Less
  | Cons x xs, Nil       => Greater
  | Cons x xs, Cons y ys =>
    Ordering.andThen (Nat.compare (Char.toNat x) (Char.toNat y)) (Text.compareChars xs ys)

-- Lexicographic, by scalar value. (Not JavaScript's order, which compares
-- UTF-16 code units: there, "\u{10000}" sorts before "\u{E000}".)
def Text.compare (a : Text) (b : Text) : Ordering := Text.compareChars (Text.toList a) (Text.toList b)

def Text.less (a : Text) (b : Text) : Bool := Ordering.isLess (Text.compare a b)

-- Whitespace, for `Text.trim`: exactly space, tab, line feed, vertical tab,
-- form feed and carriage return. Not Unicode's `White_Space`.
def Char.isSpaceCode : Nat -> Bool
  | 9  => True
  | 10 => True
  | 11 => True
  | 12 => True
  | 13 => True
  | 32 => True
  | _  => False

def Char.isSpace (c : Char) : Bool := Char.isSpaceCode (Char.toNat c)

def Text.dropSpaces : List Char -> List Char
  | Nil       => Nil
  | Cons c cs => if Char.isSpace c then Text.dropSpaces cs else Cons c cs

-- Removes whitespace (as `Char.isSpace` defines it) from both ends.
def Text.trim (t : Text) : Text := MkText (List.reverseOnto (Text.dropSpaces (List.reverseOnto (Text.dropSpaces (Text.toList t)) Nil)) Nil)

-- Numbers as text

def Nat.digitChar : Nat -> Char
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
def Nat.digitsOnto : Nat -> Nat -> List Char -> List Char
  | Zero,      n, acc => acc
  | Succ fuel, n, acc =>
    if Nat.leq n 9 then Cons (Nat.digitChar n) acc else Nat.digitsOnto fuel (n / 10) (Cons (Nat.digitChar (n % 10)) acc)

-- Decimal, without leading zeros: `Nat.toText 42` is `"42"`.
def Nat.toText (n : Nat) : Text := MkText (Nat.digitsOnto (Succ n) n Nil)

-- Itself: so `"${t}"` works when `t` is already text.
def Text.toText (t : Text) : Text := t

-- The character on its own: `'a'.toText` is `"a"`.
def Char.toText (c : Char) : Text := MkText [c]

-- `"True"` or `"False"`, as the constructors are written.
def Bool.toText : Bool -> Text
  | True  => "True"
  | False => "False"

def Maybe.andThen (f : a -> Maybe b) : Maybe a -> Maybe b
  | Nothing => Nothing
  | Just x  => f x

def Maybe.map (f : a -> b) : Maybe a -> Maybe b
  | Nothing => Nothing
  | Just x  => Just (f x)

def Char.digitValue (c : Char) : Maybe Nat := if Nat.leq 48 (Char.toNat c) then (if Nat.leq (Char.toNat c) 57 then Just (Char.toNat c - 48) else Nothing) else Nothing

def Text.readDigits (acc : Nat) : List Char -> Maybe Nat
  | Nil       => Just acc
  | Cons c cs => Maybe.andThen (\d => Text.readDigits (acc * 10 + d) cs) (Char.digitValue c)

-- A non-empty sequence of ASCII digits, and nothing else: no sign,
-- whitespace or separators. Leading zeros are allowed, so
-- `Text.toNat (Nat.toText n) = Just n` but `"007"` reads as 7.
def Text.toNat : Text -> Maybe Nat
  | MkText Nil         => Nothing
  | MkText (Cons c cs) => Text.readDigits 0 (Cons c cs)

-- Integers (docs/proposals/integers.md)

-- An integer: `OfNat n` is `n`, and `NegSucc n` is `-(n + 1)`, so each
-- integer has exactly one form. The definitions compute through `Nat`'s, so
-- they're as compact as `Nat` is, and the kernel needs nothing new.
type Int : Type =
  | OfNat (n : Nat)
  | NegSucc (n : Nat)

def Nat.toInt (n : Nat) : Int := OfNat n

-- `-x`
def Int.neg : Int -> Int
  | OfNat Zero     => OfNat Zero
  | OfNat (Succ n) => NegSucc n
  | NegSucc n      => OfNat (Succ n)

-- `m - n` for naturals, as an integer. One subtraction decides which side
-- is bigger: `n - m` is zero exactly when `n <= m`.
def Int.subNatNatFrom (m : Nat) (n : Nat) : Nat -> Int
  | Zero   => OfNat (m - n)
  | Succ k => NegSucc k

def Int.subNatNat (m : Nat) (n : Nat) : Int := Int.subNatNatFrom m n (n - m)

-- `a + b`
def Int.add : Int -> Int -> Int
  | OfNat m,   OfNat n   => OfNat (m + n)
  | OfNat m,   NegSucc n => Int.subNatNat m (Succ n)
  | NegSucc m, OfNat n   => Int.subNatNat n (Succ m)
  | NegSucc m, NegSucc n => NegSucc (Succ (m + n))

-- `a - b`
def Int.sub (a : Int) (b : Int) : Int := Int.add a (Int.neg b)

-- `a * b`. By constructors first, so `OfNat m * OfNat n` is `OfNat (m * n)`.
def Int.mul : Int -> Int -> Int
  | OfNat m,   OfNat n   => OfNat (m * n)
  | OfNat m,   NegSucc n => Int.neg (OfNat (m * Succ n))
  | NegSucc m, OfNat n   => Int.neg (OfNat (Succ m * n))
  | NegSucc m, NegSucc n => OfNat (Succ m * Succ n)

-- The sum of a list of `Int`s, as `List.sum` is of `Nat`s.
def List.sumInt (xs : List Int) : Int := List.foldLeft Int.add 0 xs

theorem List.sumIntExample : List.sumInt [3, -5, 1] = -1 := rfl

-- The sum of `f` over the elements, as an `Int`: `List.sumIntBy f xs` is
-- `List.sumInt (List.map f xs)` without building the intermediate list.
def List.sumIntBy (f : a -> Int) (xs : List a) : Int := List.foldLeft (\acc x => Int.add acc (f x)) 0 xs

theorem List.sumIntByExample : List.sumIntBy (\x => Int.sub 1 x) [1, 2, 3] = -3 := rfl

-- `|x|`, as a `Nat`.
def Int.natAbs : Int -> Nat
  | OfNat n   => n
  | NegSucc n => Succ n

-- `x` if it isn't negative, otherwise `0`.
def Int.toNat : Int -> Nat
  | OfNat n   => n
  | NegSucc n => 0

-- The two constructors are different, and each is injective.

def Int.IsOfNat : Int -> Prop
  | OfNat n   => Unit
  | NegSucc n => Void

theorem Int.ofNatNotNegSucc (m : Nat) (n : Nat) : Not (OfNat m = NegSucc n)
  | p => J (\y q => Int.IsOfNat y) Trivial p

theorem Int.negSuccNotOfNat (m : Nat) (n : Nat) : Not (NegSucc m = OfNat n)
  | p => Int.ofNatNotNegSucc n m (Eq.sym p)

theorem Int.ofNatInjective (m : Nat) (n : Nat) (p : OfNat m = OfNat n) : m = n := Eq.cong Int.toNat p

theorem Int.negSuccInjective (m : Nat) (n : Nat) (p : NegSucc m = NegSucc n) : m = n := Nat.succInjective m n (Eq.cong Int.natAbs p)

def Int.decOfNat (m : Nat) (n : Nat) : Decidable (m = n) -> Decidable (OfNat m = OfNat n)
  | Yes p => Yes (Eq.cong OfNat p)
  | No r  => No (\p => r (Int.ofNatInjective m n p))

def Int.decNegSucc (m : Nat) (n : Nat) : Decidable (m = n) -> Decidable (NegSucc m = NegSucc n)
  | Yes p => Yes (Eq.cong NegSucc p)
  | No r  => No (\p => r (Int.negSuccInjective m n p))

-- For two integers this computes `Yes rfl` or a `No` of constant size,
-- however big they are, since `Nat.decEq` does.
def Int.decEq : (a : Int) -> (b : Int) -> Decidable (a = b)
  | OfNat m,   OfNat n   => Int.decOfNat m n (Nat.decEq m n)
  | OfNat m,   NegSucc n => No (Int.ofNatNotNegSucc m n)
  | NegSucc m, OfNat n   => No (Int.negSuccNotOfNat m n)
  | NegSucc m, NegSucc n => Int.decNegSucc m n (Nat.decEq m n)

-- `a <= b`. Every negative is below every non-negative; among negatives the
-- order flips, since `NegSucc n` is `-(n+1)`.
def Int.leq : Int -> Int -> Bool
  | OfNat m,   OfNat n   => Nat.leq m n
  | OfNat m,   NegSucc n => False
  | NegSucc m, OfNat n   => True
  | NegSucc m, NegSucc n => Nat.leq n m

-- `a < b`
def Int.less : Int -> Int -> Bool
  | OfNat m,   OfNat n   => Nat.leq (Succ m) n
  | OfNat m,   NegSucc n => False
  | NegSucc m, OfNat n   => True
  | NegSucc m, NegSucc n => Nat.leq (Succ n) m

def Int.LessEq (a : Int) (b : Int) : Prop := Int.leq a b = True

def Int.LessThan (a : Int) (b : Int) : Prop := Int.less a b = True

def Int.decLessEq (a : Int) (b : Int) : Decidable (Int.LessEq a b) := Bool.decTrue (Int.leq a b)

def Int.decLessThan (a : Int) (b : Int) : Decidable (Int.LessThan a b) := Bool.decTrue (Int.less a b)

def Int.compare : Int -> Int -> Ordering
  | OfNat m,   OfNat n   => Nat.compare m n
  | OfNat m,   NegSucc n => Greater
  | NegSucc m, OfNat n   => Less
  | NegSucc m, NegSucc n => Nat.compare n m

-- `|x|`, as an `Int`.
def Int.abs : Int -> Int
  | OfNat n   => OfNat n
  | NegSucc n => OfNat (Succ n)

-- `Just x` if `x` isn't negative, otherwise `Nothing`.
def Int.toNatChecked : Int -> Maybe Nat
  | OfNat n   => Just n
  | NegSucc n => Nothing

-- `-1`, `0` or `1`.
def Int.sign : Int -> Int
  | OfNat Zero     => OfNat Zero
  | OfNat (Succ n) => OfNat 1
  | NegSucc n      => NegSucc 0

-- Decimal, with a `-` in front of a negative: `"-42"`. Never `"-0"`.
def Int.toText : Int -> Text
  | OfNat n   => Nat.toText n
  | NegSucc n => MkText (Cons '-' (Text.toList (Nat.toText (Succ n))))

-- An optional `-`, then one or more ASCII digits, and nothing else. Leading
-- zeros are fine and `"-0"` is `0`; `"-"`, `""` and `"+5"` are `Nothing`.
def Text.toInt : Text -> Maybe Int
  | MkText Nil         => Nothing
  | MkText (Cons c cs) =>
    if Nat.equal (Char.toNat c) 45
    then Maybe.map (\n => Int.neg (OfNat n)) (Text.toNat (MkText cs))
    else Maybe.map OfNat (Text.toNat (MkText (Cons c cs)))

-- Division. `a / d` and `a % d` are Euclidean: `a = d * (a / d) + a % d`
-- with `0 <= a % d < |d|`, whatever the signs, so `-18 % 100` is `82`.
-- Each case divides naturals by a `Succ n`, which `auto` sees isn't zero.
-- The divisor can't be zero, but the case still has to be covered: `ok`
-- rules it out.
def Int.div : (a : Int) -> (d : Int) -> [auto ok : d != OfNat 0] -> Int
  | a,         OfNat Zero     => Void.absurd (ok rfl)
  | OfNat m,   OfNat (Succ n) => OfNat (m / Succ n)
  | NegSucc m, OfNat (Succ n) => NegSucc (m / Succ n)
  | OfNat m,   NegSucc n      => Int.neg (OfNat (m / Succ n))
  | NegSucc m, NegSucc n      => OfNat (Succ (m / Succ n))

-- Never negative. For `NegSucc m`, `m % Succ n <= n`, so the subtraction
-- doesn't stop at zero.
def Int.mod : (a : Int) -> (d : Int) -> [auto ok : d != OfNat 0] -> Int
  | a,         OfNat Zero     => Void.absurd (ok rfl)
  | OfNat m,   OfNat (Succ n) => OfNat (m % Succ n)
  | NegSucc m, OfNat (Succ n) => OfNat (n - m % Succ n)
  | OfNat m,   NegSucc n      => OfNat (m % Succ n)
  | NegSucc m, NegSucc n      => OfNat (n - m % Succ n)

-- `x % d` as a `Nat`, for indexing: `(x.modNat d).toInt = x % d.toInt`.
def Int.modNat : Int -> (d : Nat) -> [auto ok : d != 0] -> Nat
  | x,         Zero   => Void.absurd (ok rfl)
  | OfNat m,   Succ n => m % Succ n
  | NegSucc m, Succ n => n - m % Succ n

-- Truncating division, rounding toward zero; the remainder has the
-- dividend's sign (C, Rust's `/` and `%`, JavaScript's `BigInt`).
def Int.tdiv : (a : Int) -> (d : Int) -> [auto ok : d != OfNat 0] -> Int
  | a,         OfNat Zero     => Void.absurd (ok rfl)
  | OfNat m,   OfNat (Succ n) => OfNat (m / Succ n)
  | NegSucc m, OfNat (Succ n) => Int.neg (OfNat (Succ m / Succ n))
  | OfNat m,   NegSucc n      => Int.neg (OfNat (m / Succ n))
  | NegSucc m, NegSucc n      => OfNat (Succ m / Succ n)

def Int.tmod : (a : Int) -> (d : Int) -> [auto ok : d != OfNat 0] -> Int
  | a,         OfNat Zero     => Void.absurd (ok rfl)
  | OfNat m,   OfNat (Succ n) => OfNat (m % Succ n)
  | NegSucc m, OfNat (Succ n) => Int.neg (OfNat (Succ m % Succ n))
  | OfNat m,   NegSucc n      => OfNat (m % Succ n)
  | NegSucc m, NegSucc n      => Int.neg (OfNat (Succ m % Succ n))

-- Flooring division, rounding toward negative infinity; the remainder has
-- the divisor's sign (Python, Haskell's `div` and `mod`). The same as
-- Euclidean division when the divisor is positive.
def Int.fdiv : (a : Int) -> (d : Int) -> [auto ok : d != OfNat 0] -> Int
  | a,              OfNat Zero     => Void.absurd (ok rfl)
  | OfNat m,        OfNat (Succ n) => OfNat (m / Succ n)
  | NegSucc m,      OfNat (Succ n) => NegSucc (m / Succ n)
  | OfNat Zero,     NegSucc n      => OfNat Zero
  | OfNat (Succ m), NegSucc n      => NegSucc (m / Succ n)
  | NegSucc m,      NegSucc n      => OfNat (Succ m / Succ n)

def Int.fmod : (a : Int) -> (d : Int) -> [auto ok : d != OfNat 0] -> Int
  | a,              OfNat Zero     => Void.absurd (ok rfl)
  | OfNat m,        OfNat (Succ n) => OfNat (m % Succ n)
  | NegSucc m,      OfNat (Succ n) => OfNat (n - m % Succ n)
  | OfNat Zero,     NegSucc n      => OfNat Zero
  | OfNat (Succ m), NegSucc n      => Int.neg (OfNat (n - m % Succ n))
  | NegSucc m,      NegSucc n      => Int.neg (OfNat (Succ m % Succ n))

-- Lemmas (checkpoint 1)

theorem Int.toNatCheckedToInt (n : Nat) : Int.toNatChecked (Nat.toInt n) = Just n := rfl

theorem Int.negNeg : (x : Int) -> Int.neg (Int.neg x) = x
  | OfNat Zero     => rfl
  | OfNat (Succ n) => rfl
  | NegSucc n      => rfl

-- These hold by computation; stating them keeps it that way.
theorem Int.toIntAdd (m : Nat) (n : Nat) : Nat.toInt (m + n) = Int.add (Nat.toInt m) (Nat.toInt n) := rfl

theorem Int.toIntMul (m : Nat) (n : Nat) : Nat.toInt (m * n) = Int.mul (Nat.toInt m) (Nat.toInt n) := rfl

theorem Int.toNatToInt (n : Nat) : Int.toNat (Nat.toInt n) = n := rfl

theorem Int.natAbsToInt (n : Nat) : Int.natAbs (Nat.toInt n) = n := rfl

theorem Int.natAbsNeg : (x : Int) -> Int.natAbs (Int.neg x) = Int.natAbs x
  | OfNat Zero     => rfl
  | OfNat (Succ n) => rfl
  | NegSucc n      => rfl

-- Lemmas (checkpoint 2): division.
--
-- The divisor's proof is an `auto` argument, so at a use such as
-- `Int.divAddMod x 7` it's found the same way as in `x / 7`, and the two
-- terms match: a stuck `x % 7` keeps its proof in it.

theorem Nat.toIntNeZero (d : Nat) (ok : d != 0) : Nat.toInt d != 0
  | p => ok (Int.ofNatInjective d 0 p)

-- `x.modNat d < d`; `Int.modNatLt x 100` is the dial's `x.modNat 100 < 100`.
theorem Int.modNatLt : (x : Int) -> (d : Nat) -> [auto ok : d != 0] -> Int.modNat x d < d
  | x,         Zero   => Void.exfalso (ok rfl)
  | OfNat m,   Succ n => Nat.modLess m (Succ n) (Nat.succNotZero n)
  | NegSucc m, Succ n => Nat.subLe n (m % Succ n)

-- For a variable `d`, pass `[ok2 := Nat.toIntNeZero d ok]`.
theorem Int.modNatToInt : (x : Int) -> (d : Nat) -> [auto ok : d != 0] -> [auto ok2 : Nat.toInt d != 0] ->
    Nat.toInt (Int.modNat x d) = x % Nat.toInt d
  | x,         Zero   => Void.exfalso (ok rfl)
  | OfNat m,   Succ n => rfl
  | NegSucc m, Succ n => rfl

theorem Int.toIntDiv (n : Nat) : (d : Nat) -> [auto ok : d != 0] -> [auto ok2 : Nat.toInt d != 0] ->
    Nat.toInt (n / d) = Nat.toInt n / Nat.toInt d
  | Zero   => Void.exfalso (ok rfl)
  | Succ d => rfl

theorem Int.toIntMod (n : Nat) : (d : Nat) -> [auto ok : d != 0] -> [auto ok2 : Nat.toInt d != 0] ->
    Nat.toInt (n % d) = Nat.toInt n % Nat.toInt d
  | Zero   => Void.exfalso (ok rfl)
  | Succ d => rfl

-- Remainder bounds: `0 <= a % d < |d|`.
theorem Int.modNonneg : (a : Int) -> (d : Int) -> [auto ok : d != 0] -> 0 <= a % d
  | a,         OfNat Zero     => Void.exfalso (ok rfl)
  | OfNat m,   OfNat (Succ n) => rfl
  | NegSucc m, OfNat (Succ n) => rfl
  | OfNat m,   NegSucc n      => rfl
  | NegSucc m, NegSucc n      => rfl

theorem Int.modLtAbs : (a : Int) -> (d : Int) -> [auto ok : d != 0] -> a % d < Nat.toInt (Int.natAbs d)
  | a,         OfNat Zero     => Void.exfalso (ok rfl)
  | OfNat m,   OfNat (Succ n) => Nat.modLess m (Succ n) (Nat.succNotZero n)
  | NegSucc m, OfNat (Succ n) => Nat.subLe n (m % Succ n)
  | OfNat m,   NegSucc n      => Nat.modLess m (Succ n) (Nat.succNotZero n)
  | NegSucc m, NegSucc n      => Nat.subLe n (m % Succ n)

-- The division law's negative-dividend cases. With `q = m / Succ n` and
-- `r = m % Succ n`, `d * (a / d)` computes to `NegSucc (q + n * Succ q)`,
-- and adding `n - r` gives `-(m + 1)`: `Succ (q + n * Succ q) - (n - r)`
-- is `Succ m`, because `q + n * Succ q = m + (n - r)`.
theorem Int.divAddModNeg (m : Nat) (n : Nat) (q : Nat) (r : Nat) (h : m = q * Succ n + r) (hr : r <= n) :
    Int.add (NegSucc (q + n * Succ q)) (OfNat (n - r)) = NegSucc m :=
  Eq.cong (Int.subNatNatFrom (n - r) (Succ (q + n * Succ q)))
    (Eq.trans
      (Eq.cong (\t => Succ t - (n - r))
        (Eq.sym
          (Eq.trans (Eq.cong (\t => t + (n - r)) h)
          (Eq.trans (Nat.addAssoc (q * Succ n) r (n - r))
          (Eq.trans (Eq.cong (\t => q * Succ n + t) (Nat.addSubCancel r n hr))
          (Eq.trans (Eq.cong (\t => t + n) (Nat.mulComm q (Succ n)))
          (Eq.trans (Nat.addAssoc q (n * q) n)
          (Eq.trans (Eq.cong (\t => q + t) (Nat.addComm (n * q) n))
                    (Eq.cong (\t => q + t) (Eq.sym (Nat.mulSucc n q)))))))))))
      (Nat.addSub (Succ m) (n - r)))

-- The non-negative dividend, negative divisor case: `Int.neg (OfNat q)`
-- only computes once `q` is split.
theorem Int.divAddModPosNeg (m : Nat) (n : Nat) : (q : Nat) -> (r : Nat) -> m = q * Succ n + r ->
    Int.add (Int.mul (NegSucc n) (Int.neg (OfNat q))) (OfNat r) = OfNat m
  | Zero, r, h =>
    Eq.trans (Eq.cong (\t => Int.add (Int.neg (OfNat t)) (OfNat r)) (Nat.mulZero n)) (Eq.cong OfNat (Eq.sym h))
  | Succ q, r, h =>
    Eq.cong OfNat (Eq.trans (Eq.cong (\t => t + r) (Nat.mulComm (Succ n) (Succ q))) (Eq.sym h))

-- The division law.
theorem Int.divAddMod : (a : Int) -> (d : Int) -> [auto ok : d != 0] -> d * (a / d) + a % d = a
  | a,         OfNat Zero     => Void.exfalso (ok rfl)
  | OfNat m,   OfNat (Succ n) =>
    Eq.cong OfNat (Eq.trans (Eq.cong (\t => t + m % Succ n) (Nat.mulComm (Succ n) (m / Succ n)))
      (Eq.sym (Nat.divMod m (Succ n) (Nat.succNotZero n))))
  | NegSucc m, OfNat (Succ n) =>
    Int.divAddModNeg m n (m / Succ n) (m % Succ n) (Nat.divMod m (Succ n) (Nat.succNotZero n))
      (Nat.modLess m (Succ n) (Nat.succNotZero n))
  | OfNat m,   NegSucc n      =>
    Int.divAddModPosNeg m n (m / Succ n) (m % Succ n) (Nat.divMod m (Succ n) (Nat.succNotZero n))
  | NegSucc m, NegSucc n      =>
    Int.divAddModNeg m n (m / Succ n) (m % Succ n) (Nat.divMod m (Succ n) (Nat.succNotZero n))
      (Nat.modLess m (Succ n) (Nat.succNotZero n))

-- Addition laws, after Lean's core: case analysis on the constructors plus
-- lemmas about `Int.subNatNat`.
theorem Int.subNatNatZeroRight : (m : Nat) -> Int.subNatNat m 0 = OfNat m
  | Zero   => rfl
  | Succ m => rfl

theorem Int.subNatNatSelf (n : Nat) : Int.subNatNat n n = OfNat 0 :=
  Eq.trans (Eq.cong (Int.subNatNatFrom n n) (Nat.subSelf n)) (Eq.cong OfNat (Nat.subSelf n))

theorem Int.subNatNatFromSucc (m : Nat) (n : Nat) : (t : Nat) ->
    Int.subNatNatFrom (Succ m) (Succ n) t = Int.subNatNatFrom m n t
  | Zero   => rfl
  | Succ t => rfl

theorem Int.subNatNatSucc (m : Nat) (n : Nat) : Int.subNatNat (Succ m) (Succ n) = Int.subNatNat m n := Int.subNatNatFromSucc m n (n - m)

theorem Int.negSubNatNat : (m : Nat) -> (n : Nat) -> Int.neg (Int.subNatNat m n) = Int.subNatNat n m
  | Zero,   Zero   => rfl
  | Zero,   Succ n => rfl
  | Succ m, Zero   => rfl
  | Succ m, Succ n =>
    Eq.trans (Eq.cong Int.neg (Int.subNatNatSucc m n))
      (Eq.trans (Int.negSubNatNat m n) (Eq.sym (Int.subNatNatSucc n m)))

theorem Int.addZero : (a : Int) -> Int.add a (OfNat 0) = a
  | OfNat m   => Eq.cong OfNat (Nat.addZero m)
  | NegSucc m => rfl

theorem Int.zeroAdd : (a : Int) -> Int.add (OfNat 0) a = a
  | OfNat m   => rfl
  | NegSucc m => rfl

theorem Int.addComm : (a : Int) -> (b : Int) -> Int.add a b = Int.add b a
  | OfNat m,   OfNat n   => Eq.cong OfNat (Nat.addComm m n)
  | OfNat m,   NegSucc n => rfl
  | NegSucc m, OfNat n   => rfl
  | NegSucc m, NegSucc n => Eq.cong (\t => NegSucc (Succ t)) (Nat.addComm m n)

theorem Int.addNeg : (a : Int) -> Int.add a (Int.neg a) = OfNat 0
  | OfNat Zero     => rfl
  | OfNat (Succ n) => Int.subNatNatSelf (Succ n)
  | NegSucc n      => Int.subNatNatSelf (Succ n)

theorem Int.subSelf (a : Int) : Int.sub a a = OfNat 0 := Int.addNeg a

theorem Int.negAdd : (a : Int) -> (b : Int) -> Int.neg (Int.add a b) = Int.add (Int.neg a) (Int.neg b)
  | OfNat Zero,     OfNat Zero     => rfl
  | OfNat Zero,     OfNat (Succ n) => rfl
  | OfNat (Succ m), OfNat Zero     => Eq.cong NegSucc (Nat.addZero m)
  | OfNat (Succ m), OfNat (Succ n) => Eq.cong NegSucc (Nat.addSucc m n)
  | OfNat Zero,     NegSucc n      => rfl
  | OfNat (Succ m), NegSucc n      => Int.negSubNatNat (Succ m) (Succ n)
  | NegSucc m,      OfNat Zero     => Eq.cong OfNat (Eq.sym (Nat.addZero (Succ m)))
  | NegSucc m,      OfNat (Succ n) => Int.negSubNatNat (Succ n) (Succ m)
  | NegSucc m,      NegSucc n      => Eq.cong (\t => OfNat (Succ t)) (Eq.sym (Nat.addSucc m n))

-- Adding a natural number to a difference.
theorem Int.ofNatAddSubNatNat (k : Nat) : (m : Nat) -> (n : Nat) ->
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

theorem Int.subNatNatAddOfNat (k : Nat) (m : Nat) (n : Nat) :
    Int.add (Int.subNatNat m n) (OfNat k) = Int.subNatNat (m + k) n :=
  Eq.trans (Int.addComm (Int.subNatNat m n) (OfNat k)) (Int.ofNatAddSubNatNat k m n)

-- Adding a negative number to a difference.
theorem Int.negSuccAddSubNatNat (k : Nat) : (m : Nat) -> (n : Nat) ->
    Int.add (NegSucc k) (Int.subNatNat m n) = Int.subNatNat m (Succ (n + k))
  | Zero,   Zero   => rfl
  | Zero,   Succ n => Eq.cong (\t => NegSucc (Succ t)) (Nat.addComm k n)
  | Succ m, Zero   => rfl
  | Succ m, Succ n =>
    Eq.trans (Eq.cong (Int.add (NegSucc k)) (Int.subNatNatSucc m n))
      (Eq.trans (Int.negSuccAddSubNatNat k m n) (Eq.sym (Int.subNatNatSucc m (Succ (n + k)))))

theorem Int.subNatNatAddNegSucc (k : Nat) (m : Nat) (n : Nat) :
    Int.add (Int.subNatNat m n) (NegSucc k) = Int.subNatNat m (Succ (n + k)) :=
  Eq.trans (Int.addComm (Int.subNatNat m n) (NegSucc k)) (Int.negSuccAddSubNatNat k m n)

theorem Int.addAssoc : (a : Int) -> (b : Int) -> (c : Int) ->
    Int.add (Int.add a b) c = Int.add a (Int.add b c)
  | OfNat a,   OfNat b,   OfNat c   => Eq.cong OfNat (Nat.addAssoc a b c)
  | OfNat a,   OfNat b,   NegSucc c =>
    Eq.trans (Eq.cong (\t => Int.subNatNat t (Succ c)) (Nat.addComm a b))
             (Eq.sym (Int.ofNatAddSubNatNat a b (Succ c)))
  | OfNat a,   NegSucc b, OfNat c   =>
    Eq.trans (Int.subNatNatAddOfNat c a (Succ b))
      (Eq.trans (Eq.cong (\t => Int.subNatNat t (Succ b)) (Nat.addComm a c))
                (Eq.sym (Int.ofNatAddSubNatNat a c (Succ b))))
  | NegSucc a, OfNat b,   OfNat c   => Int.subNatNatAddOfNat c b (Succ a)
  | OfNat a,   NegSucc b, NegSucc c => Int.subNatNatAddNegSucc c a (Succ b)
  | NegSucc a, OfNat b,   NegSucc c =>
    Eq.trans (Int.subNatNatAddNegSucc c b (Succ a))
      (Eq.trans (Eq.cong (\t => Int.subNatNat b (Succ (Succ t))) (Nat.addComm a c))
                (Eq.sym (Int.negSuccAddSubNatNat a b (Succ c))))
  | NegSucc a, NegSucc b, OfNat c   =>
    Eq.trans (Eq.cong (\t => Int.subNatNat c (Succ (Succ t))) (Nat.addComm a b))
             (Eq.sym (Int.negSuccAddSubNatNat a c (Succ b)))
  | NegSucc a, NegSucc b, NegSucc c =>
    Eq.trans (Eq.cong (\t => NegSucc (Succ (Succ t))) (Nat.addAssoc a b c))
             (Eq.cong (\t => NegSucc (Succ t)) (Eq.sym (Nat.addSucc a (b + c))))

-- Splitting and joining

-- `Text.splitChars s cs` is the first field and the rest: never empty.
def Text.splitCons (s : Char) (c : Char) : Bool -> Pair (List Char) (List (List Char)) -> Pair (List Char) (List (List Char))
  | True,  MkPair f fs => MkPair Nil (Cons f fs)
  | False, MkPair f fs => MkPair (Cons c f) fs

def Text.splitChars (s : Char) : List Char -> Pair (List Char) (List (List Char))
  | Nil       => MkPair Nil Nil
  | Cons c cs => Text.splitCons s c (Decidable.toBool (Char.decEq c s)) (Text.splitChars s cs)

def Text.joinChars (s : Char) (f : List Char) : List (List Char) -> List Char
  | Nil       => f
  | Cons g gs => List.append f (Cons s (Text.joinChars s g gs))

def Text.joinPair (s : Char) : Pair (List Char) (List (List Char)) -> List Char
  | MkPair f fs => Text.joinChars s f fs

theorem Text.joinCons (s : Char) (c : Char) (f : List Char) : (fs : List (List Char)) ->
    Text.joinChars s (Cons c f) fs = Cons c (Text.joinChars s f fs)
  | Nil       => rfl
  | Cons g gs => rfl

theorem Text.joinSplitCons (s : Char) (c : Char) (cs : List Char) :
    (p : Pair (List Char) (List (List Char))) -> Text.joinPair s p = cs ->
    (d : Decidable (c = s)) -> Text.joinPair s (Text.splitCons s c (Decidable.toBool d) p) = Cons c cs
  | MkPair f fs, h, Yes e =>
    Eq.trans (Eq.cong (Cons s) h) (Eq.cong (\x => Cons x cs) (Eq.sym e))
  | MkPair f fs, h, No r =>
    Eq.trans (Text.joinCons s c f fs) (Eq.cong (Cons c) h)

theorem Text.joinSplitChars (s : Char) : (cs : List Char) -> Text.joinPair s (Text.splitChars s cs) = cs
  | Nil       => rfl
  | Cons c cs =>
    Text.joinSplitCons s c cs (Text.splitChars s cs) (Text.joinSplitChars s cs) (Char.decEq c s)

def Text.textsOf : List (List Char) -> List Text
  | Nil       => Nil
  | Cons f fs => Cons (MkText f) (Text.textsOf fs)

def Text.charListsOf : List Text -> List (List Char)
  | Nil       => Nil
  | Cons t ts => Cons (Text.toList t) (Text.charListsOf ts)

theorem Text.charListsOfTexts : (fs : List (List Char)) -> Text.charListsOf (Text.textsOf fs) = fs
  | Nil       => rfl
  | Cons f fs => Eq.cong (Cons f) (Text.charListsOfTexts fs)

def Text.splitTexts : Pair (List Char) (List (List Char)) -> List Text
  | MkPair f fs => Cons (MkText f) (Text.textsOf fs)

-- The fields between separators, keeping empty ones: splitting "a,,b" on
-- ',' gives ["a", "", "b"], and splitting "" gives [""].
def Text.split (s : Char) (t : Text) : List Text := Text.splitTexts (Text.splitChars s (Text.toList t))

-- The texts with `s` between them. `Text.join s (Text.split s t) = t`.
def Text.join (s : Char) : List Text -> Text
  | Nil       => MkText Nil
  | Cons t ts => MkText (Text.joinChars s (Text.toList t) (Text.charListsOf ts))

theorem Text.joinSplitTexts (s : Char) : (p : Pair (List Char) (List (List Char))) ->
    Text.join s (Text.splitTexts p) = MkText (Text.joinPair s p)
  | MkPair f fs => Eq.cong (\l => MkText (Text.joinChars s f l)) (Text.charListsOfTexts fs)

theorem Text.joinSplit (s : Char) : (t : Text) -> Text.join s (Text.split s t) = t
  | MkText cs =>
    Eq.trans (Text.joinSplitTexts s (Text.splitChars s cs)) (Eq.cong MkText (Text.joinSplitChars s cs))

-- Lines

def Char.isLineFeedCode : Nat -> Bool
  | 10 => True
  | _  => False

def Char.isCarriageReturnCode : Nat -> Bool
  | 13 => True
  | _  => False

-- A line that ended with a line feed, from its characters newest first,
-- without a carriage return just before the line feed.
def Text.endLine : List Char -> Text
  | Nil       => MkText Nil
  | Cons c cs => MkText (List.reverseOnto (if Char.isCarriageReturnCode (Char.toNat c) then cs else Cons c cs) Nil)

-- The last line, if the text doesn't end with a line feed: kept whole.
def Text.lastLine : List Char -> List Text -> List Text
  | Nil,       acc => acc
  | Cons c cs, acc => Cons (MkText (List.reverseOnto (Cons c cs) Nil)) acc

-- `line` is the current line's characters, newest first, and `acc` the
-- finished lines, newest first.
def Text.linesFrom (line : List Char) (acc : List Text) : List Char -> List Text
  | Nil       => List.reverseOnto (Text.lastLine line acc) Nil
  | Cons c cs =>
    if Char.isLineFeedCode (Char.toNat c) then Text.linesFrom Nil (Cons (Text.endLine line) acc) cs
    else Text.linesFrom (Cons c line) acc cs

-- The lines of a text, without their line endings, as Rust's `str::lines`
-- gives them. A line ends with a line feed, or a carriage return and a line
-- feed; the last line's ending is optional, so "a\nb" and "a\nb\n" both
-- give ["a", "b"], "" gives [], and "\n" gives [""]. A carriage return
-- anywhere else is kept. These are the lines `readLine` would give.
def Text.lines (t : Text) : List Text := Text.linesFrom Nil Nil (Text.toList t)

-- Computations (docs/proposals/abilities.md)

-- A computation that returns an `a`, performing operations from a signature:
-- `op` is the type of operation calls, and `res o` is what call `o` gives
-- back. Every computation is a finite tree, so folds over it terminate.
type Effect.Comp (op : Type) (res : op -> Type) (a : Type) : Type =
  | Done (value : a)
  | Call (o : op) (rest : res o -> Comp op res a)

-- The fold over a computation. `call` gets each operation together with the
-- results of folding every way it could continue, and may use them any
-- number of times. A deep handler is a fold.
def Effect.foldComp [op : Type] [res : op -> Type] [a r : Type]
    (done : a -> r) (call : (o : op) -> (res o -> r) -> r) : Comp op res a -> r
  | Done x      => done x
  | Call o rest => call o (\y => foldComp done call (rest y))

-- Sequencing: run `c`, then `next` with its result.
def Effect.bind : [op : Type] -> [res : op -> Type] -> [a b : Type] ->
    Comp op res a -> (a -> Comp op res b) -> Comp op res b
  | Done x,      next => next x
  | Call o rest, next => Call o (\y => bind (rest y) next)

-- Rows: signatures side by side, and mappings between signatures.

-- The operations of two signatures: the row `{l, r}`.
type Effect.Plus (l : Type) (r : Type) : Type =
  | L (o : l)
  | R (o : r)

def Effect.PlusRes [l r : Type] (lres : l -> Type) (rres : r -> Type) : Plus l r -> Type
  | L o => lres o
  | R o => rres o

-- A mapping from one signature into another. Because what an operation
-- returns depends on the operation, a mapping says both where each
-- operation goes and how its response comes back.
type Effect.SigMap (op1 : Type) (res1 : op1 -> Type) (op2 : Type) (res2 : op2 -> Type) : Type =
  | MkSigMap (inject : op1 -> op2) (reply : (o : op1) -> res2 (inject o) -> res1 o)

def Effect.sigInject : [op1 : Type] -> [res1 : op1 -> Type] -> [op2 : Type] -> [res2 : op2 -> Type] ->
    SigMap op1 res1 op2 res2 -> op1 -> op2
  | MkSigMap inj rep, o => inj o

def Effect.sigReply : [op1 : Type] -> [res1 : op1 -> Type] -> [op2 : Type] -> [res2 : op2 -> Type] ->
    (m : SigMap op1 res1 op2 res2) -> (o : op1) -> res2 (sigInject m o) -> res1 o
  | MkSigMap inj rep, o, r => rep o r

-- Moves a computation along a mapping. Operations stay in the same order;
-- only their names in the signature change.
def Effect.translate [op1 : Type] [res1 : op1 -> Type] [op2 : Type] [res2 : op2 -> Type] [a : Type]
    (m : SigMap op1 res1 op2 res2) : Comp op1 res1 a -> Comp op2 res2 a
  | Done x      => Done x
  | Call o rest => Call (sigInject m o) (\r => translate m (rest (sigReply m o r)))

def Effect.sigId : [op : Type] -> [res : op -> Type] -> SigMap op res op res := MkSigMap (\o => o) (\o r => r)

def Effect.sigCompose : [op1 : Type] -> [res1 : op1 -> Type] -> [op2 : Type] -> [res2 : op2 -> Type] ->
    [op3 : Type] -> [res3 : op3 -> Type] ->
    SigMap op1 res1 op2 res2 -> SigMap op2 res2 op3 res3 -> SigMap op1 res1 op3 res3
  | MkSigMap i1 r1, MkSigMap i2 r2 =>
    MkSigMap (\o => i2 (i1 o)) (\o r => r1 o (r2 (i1 o) r))

-- Weakening: a signature into a row with something else on the right or left.
def Effect.sigLeft : [l r : Type] -> [lres : l -> Type] -> [rres : r -> Type] ->
  SigMap l lres (Plus l r) (PlusRes lres rres) := MkSigMap (\o => L o) (\o x => x)

def Effect.sigRight : [l r : Type] -> [lres : l -> Type] -> [rres : r -> Type] ->
  SigMap r rres (Plus l r) (PlusRes lres rres) := MkSigMap (\o => R o) (\o x => x)

-- Reordering: `{l, r}` to `{r, l}`.
def Effect.swapOp : [l r : Type] -> Plus l r -> Plus r l
  | L o => R o
  | R o => L o

def Effect.swapReply : [l r : Type] -> [lres : l -> Type] -> [rres : r -> Type] ->
    (o : Plus l r) -> PlusRes rres lres (swapOp o) -> PlusRes lres rres o
  | L o, x => x
  | R o, x => x

def Effect.sigSwap : [l r : Type] -> [lres : l -> Type] -> [rres : r -> Type] ->
  SigMap (Plus l r) (PlusRes lres rres) (Plus r l) (PlusRes rres lres) := MkSigMap swapOp swapReply

-- Support for abilities (docs/proposals/abilities.md). The elaborator
-- translates `ability`, rows `{A | e}`, effectful code and `handle` into these.

-- `()`: the unit type and its only value.
type Builtin.UnitType : Type =
  | UnitValue

-- The signature with no operations: the end of a closed row.
type Effect.NoOp : Type

def Effect.NoRes : NoOp -> Type
  | ()

-- A signature as one value, so a row variable `e` is one parameter.
type Effect.Sig : Type 1 =
  | MkSig (op : Type) (res : op -> Type)

def Effect.sigOp : Sig -> Type
  | MkSig op res => op

def Effect.sigRes : (s : Sig) -> sigOp s -> Type
  | MkSig op res, a1 => res a1

-- Combining two mappings into one from `{l, r}`.
def Effect.caseInject [l r t : Type] [lres : l -> Type] [rres : r -> Type] [tres : t -> Type]
    (ml : SigMap l lres t tres) (mr : SigMap r rres t tres) : Plus l r -> t
  | L o => sigInject ml o
  | R o => sigInject mr o

def Effect.caseReply [l r t : Type] [lres : l -> Type] [rres : r -> Type] [tres : t -> Type]
    (ml : SigMap l lres t tres) (mr : SigMap r rres t tres) :
    (o : Plus l r) -> tres (caseInject ml mr o) -> PlusRes lres rres o
  | L o, x => sigReply ml o x
  | R o, x => sigReply mr o x

def Effect.sigCase [l r t : Type] [lres : l -> Type] [rres : r -> Type] [tres : t -> Type]
  (ml : SigMap l lres t tres) (mr : SigMap r rres t tres) : SigMap (Plus l r) (PlusRes lres rres) t tres := MkSigMap (caseInject ml mr) (caseReply ml mr)

-- The empty signature maps into anything.
def Effect.noInject : [t : Type] -> NoOp -> t
  | ()

def Effect.noReply : [t : Type] -> [tres : t -> Type] -> (o : NoOp) -> tres (noInject o) -> NoRes o
  | (), _

def Effect.sigFromNo : [t : Type] -> [tres : t -> Type] -> SigMap NoOp NoRes t tres := MkSigMap noInject noReply

-- A handler's step for the row `{l, r}`, from steps for each side.
def Effect.handlePlus [l r : Type] [lres : l -> Type] [rres : r -> Type] [res : Type]
    (fl : (o : l) -> (lres o -> res) -> res) (fr : (o : r) -> (rres o -> res) -> res) :
    (o : Plus l r) -> (PlusRes lres rres o -> res) -> res
  | L o, k => fl o k
  | R o, k => fr o k

-- A computation that performs nothing is just its result.
def Effect.runPure : [a : Type] -> Comp NoOp NoRes a -> a
  | Done x => x
  | Call () rest

-- Partial computations (docs/proposals/partial.md)

-- A recursion request: run the definition being defined again on `x`. A
-- partial definition's body makes these instead of calling itself.
type Effect.Rec (req : Type) : Type =
  | Recur (x : req)

-- What a request is answered with.
def Effect.RecRes [req : Type] (ans : req -> Type) : Rec req -> Type
  | Recur x => ans x

-- A computation that may not finish: what `{Partial | e} a` stands for.
-- These have no definitions, and nothing can look inside a `Delay`: only
-- the runtime runs one, a step at a time. The kernel admits them as
-- primitives, after checking their types are exactly these.
def Effect.Delay : (op : Type) -> (res : op -> Type) -> Type -> Type

-- Finished, with this result.
def Effect.now : [op : Type] -> [res : op -> Type] -> [a : Type] -> a -> Delay op res a

-- A computation that finishes, as one that might not.
def Effect.lift : [op : Type] -> [res : op -> Type] -> [a : Type] -> Comp op res a -> Delay op res a

-- Sequencing.
def Effect.bindD : [op : Type] -> [res : op -> Type] -> [a b : Type] ->
  Delay op res a -> (a -> Delay op res b) -> Delay op res b

-- Moves a computation along a mapping between signatures.
def Effect.mapSig : [op1 : Type] -> [res1 : op1 -> Type] -> [op2 : Type] -> [res2 : op2 -> Type] -> [a : Type] ->
  SigMap op1 res1 op2 res2 -> Delay op1 res1 a -> Delay op2 res2 a

-- The recursive function a description defines: each `Recur y` its body
-- requests is answered by running the body on `y`.
def Effect.pfix : [op : Type] -> [res : op -> Type] -> [req : Type] -> [ans : req -> Type] ->
  ((x : req) -> Delay (Plus (Rec req) op) (PlusRes (RecRes ans) res) (ans x)) ->
  (x : req) -> Delay op res (ans x)

-- Decimal digits, most significant first: `Nat.digits 1205` is `[1, 2, 0, 5]`
-- and `Nat.digits 0` is `[0]`. The fuel is `n + 1`, more than the digits need.
def Nat.digitsFuel : Nat -> Nat -> List Nat -> List Nat
  | Zero,      n, acc => Cons n acc
  | Succ fuel, n, acc =>
    if Nat.leq n 9 then Cons n acc else Nat.digitsFuel fuel (n / 10) (Cons (n % 10) acc)

def Nat.digits (n : Nat) : List Nat := Nat.digitsFuel (Succ n) n Nil

-- The number whose decimal digits these are, most significant first. Digits
-- above 9 carry into their neighbours: it is `Nat.digits`'s inverse only on
-- real digit lists.
def Nat.fromDigits (ds : List Nat) : Nat := List.foldLeft (\acc d => acc * 10 + d) 0 ds

-- `Nat.fromDigits` starting from `a` instead of 0: `a` is shifted left past
-- every digit.
theorem Nat.fromDigitsFrom : (a : Nat) -> (ds : List Nat) ->
    List.foldLeft (\acc d => acc * 10 + d) a ds = a * Nat.pow 10 (List.length ds) + Nat.fromDigits ds
  | a, Nil       => Eq.sym (Eq.trans (Nat.addZero (a * 1)) (Nat.mulOne a))
  | a, Cons d ds =>
    Eq.trans (Nat.fromDigitsFrom (a * 10 + d) ds)
      (Eq.trans (Eq.cong (\t => t + Nat.fromDigits ds) (Nat.mulDistribRight (a * 10) d (Nat.pow 10 (List.length ds))))
        (Eq.trans (Nat.addAssoc ((a * 10) * Nat.pow 10 (List.length ds)) (d * Nat.pow 10 (List.length ds)) (Nat.fromDigits ds))
          (Eq.trans (Eq.cong (\t => t + (d * Nat.pow 10 (List.length ds) + Nat.fromDigits ds)) (Nat.mulAssoc a 10 (Nat.pow 10 (List.length ds))))
            (Eq.cong (\t => a * (10 * Nat.pow 10 (List.length ds)) + t) (Eq.sym (Nat.fromDigitsFrom d ds))))))

-- The first digit counts 10^n, for the n digits after it.
theorem Nat.fromDigitsCons (d : Nat) (ds : List Nat) :
  Nat.fromDigits (Cons d ds) = d * Nat.pow 10 (List.length ds) + Nat.fromDigits ds := Nat.fromDigitsFrom d ds


theorem Nat.digitsZero : Nat.digits 0 = [0] := rfl

theorem Nat.digitsExample : Nat.digits 1205 = [1, 2, 0, 5] := rfl

theorem Nat.fromDigitsExample : Nat.fromDigits [1, 2, 0, 5] = 1205 := rfl

theorem Nat.digitsSeven : Nat.digits 7 = [7] := rfl

theorem Nat.digitsTen : Nat.digits 10 = [1, 0] := rfl

theorem Nat.fromDigitsNil : Nat.fromDigits Nil = 0 := rfl

theorem Nat.digitsRoundTrip : Nat.fromDigits (Nat.digits 9876543210) = 9876543210 := rfl

-- Input and output (docs/proposals/text-and-io.md, Part 2)

-- The console. Only a host interpreter performs these for real; in Stitchwort
-- code, `IO.simulate` interprets them as data.
ability IO where
  print    : Text -> {IO} ()          -- writes the text, then a line ending
  readLine : () -> {IO} (Maybe Text)  -- Nothing only at end of input
  readAll  : () -> {IO} Text          -- the rest of the input, all at once

-- The first line of scripted input, if there is one.
def IO.nextLine : List Text -> Maybe Text
  | Nil       => Nothing
  | Cons l ls => Just l

-- All of the scripted input, as `readAll` gives it: each line followed by a
-- line feed, as a real interpreter would read it.
def IO.restOf (ins : List Text) : Text :=
  MkText (List.concatMap (\l => List.append (Text.toList l) ['\n']) ins)

-- Runs a program against scripted input lines: each `readLine` takes the
-- next one, and gives `Nothing` once they're used up; `readAll` takes all
-- that are left (see `IO.restOf`), after which `readLine` gives `Nothing`
-- and `readAll` gives "". Records each `print` payload, in order, with the
-- result. A payload is one entry even if it contains a line feed: a real
-- interpreter writes each payload followed by a line ending. The payloads
-- are collected in reverse and turned round at the end, so a long run
-- doesn't build a deep chain of pending pairs.
def IO.simulate (input : List Text) (prog : () -> {IO | e} a) : {e} Pair (List Text) a :=
  let run : List Text -> List Text -> {e} Pair (List Text) a :=
    handle prog () with
      | return x      => \ins out => MkPair (List.reverseOnto out Nil) x
      | print t, k    => \ins out => k () ins (Cons t out)
      | readLine u, k => \ins out => k (IO.nextLine ins) (List.tailOf ins) out
      | readAll u, k  => \ins out => k (IO.restOf ins) Nil out
  run input Nil

-- Every remaining line of input, in order, as `readLine` would give them.
-- Total: the input is read all at once.
def IO.readAllLines () : {IO} (List Text) := (readAll ()).lines
