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

Not : Prop -> Prop
Not p = p -> Void

-- Both propositions hold.
type And (p : Prop) (q : Prop) : Prop =
  | Both (left : p) (right : q)

-- From a proof of `Void`, anything follows. `()` means "there's no value to
-- match here", so no right-hand side is needed.
Void.absurd : Void -> a
Void.absurd ()

-- The same for proofs. (Without universe polymorphism, `Void.absurd`'s `a` can
-- only be a type of data.)
Void.exfalso : [p : Prop] -> Void -> p
Void.exfalso ()

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
Nat.add : Nat -> Nat -> Nat
Nat.add Zero     n = n
Nat.add (Succ m) n = Succ (Nat.add m n)

-- `a - b`, stopping at zero: `3 - 5 = 0`.
Nat.sub : Nat -> Nat -> Nat
Nat.sub m        Zero     = m
Nat.sub Zero     (Succ n) = Zero
Nat.sub (Succ m) (Succ n) = Nat.sub m n

-- `a * b`
Nat.mul : Nat -> Nat -> Nat
Nat.mul Zero     n = 0
Nat.mul (Succ m) n = n + Nat.mul m n

Nat.pred : Nat -> Nat
Nat.pred Zero     = Zero
Nat.pred (Succ n) = n

-- Booleans

type Bool : Type =
  | False
  | True

Bool.not : Bool -> Bool
Bool.not False = True
Bool.not True  = False

-- `if c then a else b`. The branches take a (unused) proof of `Unit` so that
-- only the chosen one is evaluated.
Bool.ifThenElse : [a : Type] -> Bool -> (Unit -> a) -> (Unit -> a) -> a
Bool.ifThenElse True  t e = t Trivial
Bool.ifThenElse False t e = e Trivial

-- `m <= n` and `m < n` are propositions, defined by computation.
Nat.leq : Nat -> Nat -> Bool
Nat.leq Zero     n        = True
Nat.leq (Succ m) Zero     = False
Nat.leq (Succ m) (Succ n) = Nat.leq m n

Nat.LessEq : Nat -> Nat -> Prop
Nat.LessEq m n = Nat.leq m n = True

Nat.LessThan : Nat -> Nat -> Prop
Nat.LessThan m n = Nat.leq (Succ m) n = True

-- Lists

type List (a : Type) : Type =
  | Nil
  | Cons (head : a) (tail : List a)

-- `a` is bound automatically, as an implicit argument: `List.length : [a : Type] -> ...`.
List.length : List a -> Nat
List.length Nil         = 0
List.length (Cons x xs) = Succ (List.length xs)

List.append : List a -> List a -> List a
List.append Nil         ys = ys
List.append (Cons x xs) ys = Cons x (List.append xs ys)

-- A value that may be missing.
type Maybe (a : Type) : Type =
  | Nothing
  | Just (value : a)

-- Two values together.
type Pair (a : Type) (b : Type) : Type =
  | MkPair (fst : a) (snd : b)

Pair.fst : Pair a b -> a
Pair.fst (MkPair x y) = x

Pair.snd : Pair a b -> b
Pair.snd (MkPair x y) = y

-- `List.reverseOnto xs acc` is `xs` reversed, followed by `acc`.
List.reverseOnto : List a -> List a -> List a
List.reverseOnto Nil         acc = acc
List.reverseOnto (Cons x xs) acc = List.reverseOnto xs (Cons x acc)

-- Equality lemmas, all built from `J`.

theorem Eq.cong : (f : a -> b) -> [x y : a] -> x = y -> f x = f y
Eq.cong f p = J (\y' p' -> f x = f y') rfl p

theorem Eq.sym : [x y : a] -> x = y -> y = x
Eq.sym p = J (\y' p' -> y' = x) rfl p

theorem Eq.trans : [x y z : a] -> x = y -> y = z -> x = z
Eq.trans p q = J (\z' q' -> x = z') p q

-- Different constructors are different. Each proof transports along the
-- equation into a family that's `Unit` at one constructor and `Void` at the other.

Nat.IsZero : Nat -> Prop
Nat.IsZero Zero     = Unit
Nat.IsZero (Succ n) = Void

theorem Nat.zeroNotSucc : (n : Nat) -> Not (0 = Succ n)
Nat.zeroNotSucc n p = J (\y q -> Nat.IsZero y) Trivial p

theorem Nat.succNotZero : (n : Nat) -> Not (Succ n = 0)
Nat.succNotZero n p = Nat.zeroNotSucc n (Eq.sym p)

theorem Nat.succInjective : (m : Nat) -> (n : Nat) -> Succ m = Succ n -> m = n
Nat.succInjective m n p = Eq.cong Nat.pred p

Bool.IsFalse : Bool -> Prop
Bool.IsFalse False = Unit
Bool.IsFalse True  = Void

theorem Bool.falseNotTrue : Not (False = True)
Bool.falseNotTrue p = J (\y q -> Bool.IsFalse y) Trivial p

-- Whether two numbers are equal, as a `Bool`.
Nat.equal : Nat -> Nat -> Bool
Nat.equal Zero     Zero     = True
Nat.equal Zero     (Succ n) = False
Nat.equal (Succ m) Zero     = False
Nat.equal (Succ m) (Succ n) = Nat.equal m n

theorem Nat.equalRefl : (n : Nat) -> Nat.equal n n = True
Nat.equalRefl Zero     = rfl
Nat.equalRefl (Succ n) = Nat.equalRefl n

-- Numbers that `Nat.equal` says are equal are equal.
theorem Nat.equalSound : (m : Nat) -> (n : Nat) -> Nat.equal m n = True -> m = n
Nat.equalSound Zero     Zero     h = rfl
Nat.equalSound Zero     (Succ n) h = Void.exfalso (Bool.falseNotTrue h)
Nat.equalSound (Succ m) Zero     h = Void.exfalso (Bool.falseNotTrue h)
Nat.equalSound (Succ m) (Succ n) h = Eq.cong Succ (Nat.equalSound m n h)

-- Numbers that `Nat.equal` says differ are different.
theorem Nat.equalFalse : (m : Nat) -> (n : Nat) -> Nat.equal m n = False -> Not (m = n)
Nat.equalFalse m n h p = Bool.falseNotTrue (Eq.trans (Eq.sym h) (J (\y q -> Nat.equal m y = True) (Nat.equalRefl m) p))

-- Decisions

-- Either a proof of `p` or a proof that `p` is false. Whether it's `Yes` or
-- `No` exists at runtime; the proofs inside are erased.
type Decidable (p : Prop) : Type =
  | Yes (proof : p)
  | No (refutation : Not p)

-- `Decidable.IsYes d` is `Unit` (provable) exactly when `d` is `Yes`.
Decidable.IsYes : Decidable p -> Prop
Decidable.IsYes (Yes h) = Unit
Decidable.IsYes (No r)  = Void

-- How `auto` turns a decision into a proof: `Decidable.fromYes d Trivial` only checks
-- when `d` computes to `Yes`.
Decidable.fromYes : [p : Prop] -> (d : Decidable p) -> Decidable.IsYes d -> p
Decidable.fromYes (Yes h) u = h
Decidable.fromYes (No r)  u = Void.exfalso u

-- `a == b` is `Decidable.toBool d`, for a decision procedure `d` for `a = b`.
Decidable.toBool : [p : Prop] -> Decidable p -> Bool
Decidable.toBool (Yes h) = True
Decidable.toBool (No r)  = False

-- `if h : p then a else b`
Decidable.elim : [p : Prop] -> [a : Type] -> Decidable p -> (p -> a) -> (Not p -> a) -> a
Decidable.elim (Yes h) yes no = yes h
Decidable.elim (No r)  yes no = no r

-- Decision procedures. `auto` and `if h : …` use any function returning
-- `Decidable …`.

Bool.decTrue : (b : Bool) -> Decidable (b = True)
Bool.decTrue True  = Yes rfl
Bool.decTrue False = No Bool.falseNotTrue

Nat.decSucc : (m : Nat) -> (n : Nat) -> Decidable (m = n) -> Decidable (Succ m = Succ n)
Nat.decSucc m n (Yes p) = Yes (Eq.cong Succ p)
Nat.decSucc m n (No r)  = No (\p -> r (Nat.succInjective m n p))

-- A decision from what `Nat.equal` says.
Nat.decEqFrom : (m : Nat) -> (n : Nat) -> (b : Bool) -> Nat.equal m n = b -> Decidable (m = n)
Nat.decEqFrom m n True  h = Yes (Nat.equalSound m n h)
Nat.decEqFrom m n False h = No (Nat.equalFalse m n h)

-- For two numbers this computes `Yes rfl` or `No (Nat.equalFalse m n rfl)`, and the
-- native gives exactly that, however big they are. (Recursing with `Nat.decSucc`
-- would build a refutation as deep as the smaller number.) It matches on
-- both numbers so it waits until they're known, rather than unfolding around
-- an unknown one.
Nat.decEq : (m : Nat) -> (n : Nat) -> Decidable (m = n)
Nat.decEq Zero     Zero     = Yes rfl
Nat.decEq Zero     (Succ n) = No (Nat.equalFalse 0 (Succ n) rfl)
Nat.decEq (Succ m) Zero     = No (Nat.equalFalse (Succ m) 0 rfl)
Nat.decEq (Succ m) (Succ n) = Nat.decEqFrom (Succ m) (Succ n) (Nat.equal m n) rfl

theorem Bool.trueNotFalse : Not (True = False)
Bool.trueNotFalse p = Bool.falseNotTrue (Eq.sym p)

Bool.decEq : (a : Bool) -> (b : Bool) -> Decidable (a = b)
Bool.decEq False False = Yes rfl
Bool.decEq False True  = No Bool.falseNotTrue
Bool.decEq True  False = No Bool.trueNotFalse
Bool.decEq True  True  = Yes rfl

Decidable.not : [p : Prop] -> Decidable p -> Decidable (Not p)
Decidable.not (Yes h) = No (\n -> n h)
Decidable.not (No r)  = Yes r

Nat.decLessEq : (m : Nat) -> (n : Nat) -> Decidable (m <= n)
Nat.decLessEq m n = Bool.decTrue (Nat.leq m n)

Nat.decLessThan : (m : Nat) -> (n : Nat) -> Decidable (m < n)
Nat.decLessThan m n = Bool.decTrue (Nat.leq (Succ m) n)

-- Proofs that two booleans are equal are unique. This is Hedberg's argument,
-- which works for any type with decidable equality: `Bool.canon` turns any proof
-- of `x = y` into one chosen by `Bool.decEq`, so it ignores which proof it was
-- given, and every proof can be recovered from its canonical one.
Bool.canon : [x y : Bool] -> Decidable (x = y) -> x = y -> x = y
Bool.canon (Yes e) p = e
Bool.canon (No r)  p = Void.exfalso (r p)

theorem Bool.canonConst : [x y : Bool] -> (d : Decidable (x = y)) -> (p : x = y) -> (q : x = y) ->
  Bool.canon d p = Bool.canon d q
Bool.canonConst (Yes e) p q = rfl
Bool.canonConst (No r)  p q = Void.exfalso (r p)

theorem Bool.symThenSelf : [x y : Bool] -> (q : x = y) -> rfl = Eq.trans (Eq.sym q) q
Bool.symThenSelf q = J (\y' q' -> rfl = Eq.trans (Eq.sym q') q') rfl q

theorem Bool.fromCanon : (x : Bool) -> (y : Bool) -> (p : x = y) ->
  p = Eq.trans (Eq.sym (Bool.canon (Bool.decEq x x) rfl)) (Bool.canon (Bool.decEq x y) p)
Bool.fromCanon x y p =
  J (\y' p' -> p' = Eq.trans (Eq.sym (Bool.canon (Bool.decEq x x) rfl)) (Bool.canon (Bool.decEq x y') p'))
    (Bool.symThenSelf (Bool.canon (Bool.decEq x x) rfl)) p

theorem Bool.uniqueEq : (x : Bool) -> (y : Bool) -> (p : x = y) -> (q : x = y) -> p = q
Bool.uniqueEq x y p q =
  J (\z e -> p = z)
    (J (\r e -> p = Eq.trans (Eq.sym (Bool.canon (Bool.decEq x x) rfl)) r)
      (Bool.fromCanon x y p) (Bool.canonConst (Bool.decEq x y) p q))
    (J (\z e -> z = q) rfl (Bool.fromCanon x y q))

-- Characters

-- Whether a number is a Unicode scalar value: at most 0x10FFFF, and not a
-- surrogate (0xD800 to 0xDFFF).
Char.isScalar : Nat -> Bool
Char.isScalar n = if Nat.leq 55296 n then (if Nat.leq n 57343 then False else Nat.leq n 1114111) else True

-- A Unicode scalar value. `'a'` is a `Char`; the compiler proves `valid` for
-- a literal by computation, and the kernel checks it.
type Char : Type =
  | MkChar (code : Nat) (valid : Char.isScalar code = True)

Char.toNat : Char -> Nat
Char.toNat (MkChar n v) = n

Char.fromNat : Nat -> Maybe Char
Char.fromNat n = if h : Char.isScalar n = True then Just (MkChar n h) else Nothing

-- Characters with the same code are equal: their proofs of `valid` are too.
theorem Char.mkExt : (a : Nat) -> (b : Nat) -> (p : Char.isScalar a = True) -> a = b ->
  (q : Char.isScalar b = True) -> MkChar a p = MkChar b q
Char.mkExt a b p e =
  J (\b' e' -> (q' : Char.isScalar b' = True) -> MkChar a p = MkChar b' q')
    (\q' -> J (\r e'' -> MkChar a p = MkChar a r) rfl (Bool.uniqueEq (Char.isScalar a) True p q'))
    e

theorem Char.ext : (x : Char) -> (y : Char) -> Char.toNat x = Char.toNat y -> x = y
Char.ext (MkChar a p) (MkChar b q) e = Char.mkExt a b p e q

Char.decEqFrom : (x : Char) -> (y : Char) -> Decidable (Char.toNat x = Char.toNat y) -> Decidable (x = y)
Char.decEqFrom x y (Yes e) = Yes (Char.ext x y e)
Char.decEqFrom x y (No r)  = No (\p -> r (Eq.cong Char.toNat p))

Char.decEq : (x : Char) -> (y : Char) -> Decidable (x = y)
Char.decEq x y = Char.decEqFrom x y (Nat.decEq (Char.toNat x) (Char.toNat y))

-- Division

-- Counts how many times `d` fits into `n`, using `fuel` to stay structurally
-- recursive (`n` is always enough fuel when `d` isn't zero).
Nat.divFuel : Nat -> Nat -> Nat -> Nat
Nat.divFuel Zero        n d = 0
Nat.divFuel (Succ fuel) n d = if Nat.leq d n then Succ (Nat.divFuel fuel (n - d) d) else 0

-- `n / d` and `n % d` need a proof that `d` isn't zero, which `auto` finds.
Nat.div : (n : Nat) -> (d : Nat) -> [auto ok : d != 0] -> Nat
Nat.div n d = Nat.divFuel n n d

Nat.mod : (n : Nat) -> (d : Nat) -> [auto ok : d != 0] -> Nat
Nat.mod n d = n - d * (n / d)

-- Arithmetic lemmas: addition, multiplication, order and subtraction facts proved
-- by induction, then the division law and `n % d < d`.

theorem Nat.addZero : (n : Nat) -> n + 0 = n
Nat.addZero Zero = rfl
Nat.addZero (Succ n) = Eq.cong Succ (Nat.addZero n)

theorem Nat.addSucc : (n : Nat) -> (m : Nat) -> n + Succ m = Succ (n + m)
Nat.addSucc Zero m = rfl
Nat.addSucc (Succ n) m = Eq.cong Succ (Nat.addSucc n m)

theorem Nat.addComm : (m : Nat) -> (n : Nat) -> m + n = n + m
Nat.addComm Zero n = Eq.sym (Nat.addZero n)
Nat.addComm (Succ m) n = Eq.trans (Eq.cong Succ (Nat.addComm m n)) (Eq.sym (Nat.addSucc n m))

theorem Nat.addAssoc : (a : Nat) -> (b : Nat) -> (c : Nat) -> (a + b) + c = a + (b + c)
Nat.addAssoc Zero b c = rfl
Nat.addAssoc (Succ a) b c = Eq.cong Succ (Nat.addAssoc a b c)

theorem Nat.addCancelLeft : (a : Nat) -> (b : Nat) -> (c : Nat) -> a + b = a + c -> b = c
Nat.addCancelLeft Zero b c h = h
Nat.addCancelLeft (Succ a) b c h = Nat.addCancelLeft a b c (Nat.succInjective (a + b) (a + c) h)

theorem Nat.mulZero : (n : Nat) -> n * 0 = 0
Nat.mulZero Zero = rfl
Nat.mulZero (Succ n) = Nat.mulZero n

theorem Nat.mulOne : (n : Nat) -> n * 1 = n
Nat.mulOne Zero = rfl
Nat.mulOne (Succ n) = Eq.cong Succ (Nat.mulOne n)

theorem Nat.mulSucc : (n : Nat) -> (m : Nat) -> n * Succ m = n + n * m
Nat.mulSucc Zero m = rfl
Nat.mulSucc (Succ n) m = Eq.cong Succ (Eq.trans (Eq.cong (\t -> m + t) (Nat.mulSucc n m)) (Eq.trans (Eq.sym (Nat.addAssoc m n (n * m))) (Eq.trans (Eq.cong (\t -> t + n * m) (Nat.addComm m n)) (Nat.addAssoc n m (n * m)))))

theorem Nat.mulComm : (n : Nat) -> (m : Nat) -> n * m = m * n
Nat.mulComm Zero m = Eq.sym (Nat.mulZero m)
Nat.mulComm (Succ n) m = Eq.trans (Eq.cong (\t -> m + t) (Nat.mulComm n m)) (Eq.sym (Nat.mulSucc m n))

theorem Nat.mulDistribRight : (a : Nat) -> (b : Nat) -> (c : Nat) -> (a + b) * c = a * c + b * c
Nat.mulDistribRight Zero b c = rfl
Nat.mulDistribRight (Succ a) b c = Eq.trans (Eq.cong (\t -> c + t) (Nat.mulDistribRight a b c)) (Eq.sym (Nat.addAssoc c (a * c) (b * c)))

theorem Nat.mulDistribLeft : (a : Nat) -> (b : Nat) -> (c : Nat) -> a * (b + c) = a * b + a * c
Nat.mulDistribLeft a b c = Eq.trans (Nat.mulComm a (b + c)) (Eq.trans (Nat.mulDistribRight b c a) (Eq.trans (Eq.cong (\t -> t + c * a) (Nat.mulComm b a)) (Eq.cong (\t -> a * b + t) (Nat.mulComm c a))))

theorem Nat.mulAssoc : (a : Nat) -> (b : Nat) -> (c : Nat) -> (a * b) * c = a * (b * c)
Nat.mulAssoc Zero b c = rfl
Nat.mulAssoc (Succ a) b c = Eq.trans (Nat.mulDistribRight b (a * b) c) (Eq.cong (\t -> b * c + t) (Nat.mulAssoc a b c))

theorem Nat.leRefl : (n : Nat) -> n <= n
Nat.leRefl Zero = rfl
Nat.leRefl (Succ n) = Nat.leRefl n

theorem Nat.zeroLe : (n : Nat) -> 0 <= n
Nat.zeroLe n = rfl

theorem Nat.leSucc : (n : Nat) -> n <= Succ n
Nat.leSucc Zero = rfl
Nat.leSucc (Succ n) = Nat.leSucc n

theorem Nat.leTrans : (a : Nat) -> (b : Nat) -> (c : Nat) -> a <= b -> b <= c -> a <= c
Nat.leTrans Zero b c h1 h2 = rfl
Nat.leTrans (Succ a) Zero c h1 h2 = Void.exfalso (Bool.falseNotTrue h1)
Nat.leTrans (Succ a) (Succ b) Zero h1 h2 = Void.exfalso (Bool.falseNotTrue h2)
Nat.leTrans (Succ a) (Succ b) (Succ c) h1 h2 = Nat.leTrans a b c h1 h2

theorem Nat.leAntisym : (a : Nat) -> (b : Nat) -> a <= b -> b <= a -> a = b
Nat.leAntisym Zero Zero h1 h2 = rfl
Nat.leAntisym Zero (Succ b) h1 h2 = Void.exfalso (Bool.falseNotTrue h2)
Nat.leAntisym (Succ a) Zero h1 h2 = Void.exfalso (Bool.falseNotTrue h1)
Nat.leAntisym (Succ a) (Succ b) h1 h2 = Eq.cong Succ (Nat.leAntisym a b h1 h2)

theorem Nat.leAddRight : (n : Nat) -> (m : Nat) -> n <= n + m
Nat.leAddRight Zero m = rfl
Nat.leAddRight (Succ n) m = Nat.leAddRight n m

theorem Nat.leAddLeft : (n : Nat) -> (m : Nat) -> m <= n + m
Nat.leAddLeft Zero m = Nat.leRefl m
Nat.leAddLeft (Succ n) m = Nat.leTrans m (n + m) (Succ (n + m)) (Nat.leAddLeft n m) (Nat.leSucc (n + m))

theorem Nat.leqSuccSelf : (n : Nat) -> Nat.leq (Succ n) n = False
Nat.leqSuccSelf Zero = rfl
Nat.leqSuccSelf (Succ n) = Nat.leqSuccSelf n

theorem Nat.lessIrrefl : (n : Nat) -> Not (n < n)
Nat.lessIrrefl n h = Bool.falseNotTrue (Eq.trans (Eq.sym (Nat.leqSuccSelf n)) h)

theorem Nat.lessLe : (m : Nat) -> (n : Nat) -> m < n -> m <= n
Nat.lessLe m n h = Nat.leTrans m (Succ m) n (Nat.leSucc m) h

theorem Nat.lessTrans : (m : Nat) -> (n : Nat) -> (p : Nat) -> m < n -> n < p -> m < p
Nat.lessTrans m n p h1 h2 = Nat.leTrans (Succ m) n p h1 (Nat.lessLe n p h2)

theorem Nat.leLessSucc : (m : Nat) -> (n : Nat) -> m <= n -> m < Succ n
Nat.leLessSucc m n h = h

theorem Nat.subSelf : (n : Nat) -> n - n = 0
Nat.subSelf Zero = rfl
Nat.subSelf (Succ n) = Nat.subSelf n

theorem Nat.addSub : (n : Nat) -> (m : Nat) -> (n + m) - m = n
Nat.addSub n Zero = Nat.addZero n
Nat.addSub n (Succ m) = Eq.trans (Eq.cong (\t -> t - Succ m) (Nat.addSucc n m)) (Nat.addSub n m)

theorem Nat.subLe : (n : Nat) -> (m : Nat) -> n - m <= n
Nat.subLe n Zero = Nat.leRefl n
Nat.subLe Zero (Succ m) = rfl
Nat.subLe (Succ n) (Succ m) = Nat.leTrans (n - m) n (Succ n) (Nat.subLe n m) (Nat.leSucc n)
theorem Nat.leCongLeft : (a : Nat) -> (b : Nat) -> (n : Nat) -> a = b -> a <= n -> b <= n
Nat.leCongLeft a b n p h = J (\y q -> y <= n) h p

theorem Nat.leCongRight : (a : Nat) -> (b : Nat) -> (n : Nat) -> b = n -> a <= b -> a <= n
Nat.leCongRight a b n p h = J (\y q -> a <= y) h p

theorem Nat.ltCongLeft : (a : Nat) -> (b : Nat) -> (n : Nat) -> a = b -> a < n -> b < n
Nat.ltCongLeft a b n p h = J (\y q -> y < n) h p

theorem Nat.ltCongRight : (a : Nat) -> (b : Nat) -> (n : Nat) -> b = n -> a < b -> a < n
Nat.ltCongRight a b n p h = J (\y q -> a < y) h p

theorem Nat.leAddCong : (d : Nat) -> (a : Nat) -> (b : Nat) -> a <= b -> d + a <= d + b
Nat.leAddCong Zero a b h = h
Nat.leAddCong (Succ d) a b h = Nat.leAddCong d a b h

theorem Nat.ltAddCong : (d : Nat) -> (a : Nat) -> (b : Nat) -> a < b -> d + a < d + b
Nat.ltAddCong Zero a b h = h
Nat.ltAddCong (Succ d) a b h = Nat.ltAddCong d a b h

theorem Nat.addSubCancel : (d : Nat) -> (n : Nat) -> d <= n -> d + (n - d) = n
Nat.addSubCancel Zero n h = rfl
Nat.addSubCancel (Succ d) Zero h = Void.exfalso (Bool.falseNotTrue h)
Nat.addSubCancel (Succ d) (Succ n) h = Eq.cong Succ (Nat.addSubCancel d n h)

theorem Nat.leqFalse : (d : Nat) -> (n : Nat) -> Nat.leq d n = False -> n < d
Nat.leqFalse Zero n h = Void.exfalso (Bool.trueNotFalse h)
Nat.leqFalse (Succ d) Zero h = rfl
Nat.leqFalse (Succ d) (Succ n) h = Nat.leqFalse d n h

theorem Nat.subLtAdd : (n : Nat) -> (x : Nat) -> (d : Nat) -> x <= n -> n < d + x -> n - x < d
Nat.subLtAdd n Zero d hx h = Nat.ltCongRight n (d + 0) d (Nat.addZero d) h
Nat.subLtAdd Zero (Succ x) d hx h = Void.exfalso (Bool.falseNotTrue hx)
Nat.subLtAdd (Succ n) (Succ x) d hx h = Nat.subLtAdd n x d hx (Nat.ltCongRight (Succ n) (d + Succ x) (Succ (d + x)) (Nat.addSucc d x) h)

theorem Nat.divFuelLeStep : (fuel : Nat) -> (n : Nat) -> (d : Nat) -> (b : Bool) -> Nat.leq d n = b ->
    ((m : Nat) -> d * Nat.divFuel fuel m d <= m) ->
    d * (if b then Succ (Nat.divFuel fuel (n - d) d) else 0) <= n
Nat.divFuelLeStep fuel n d True h ih =
  Nat.leCongLeft (d + d * Nat.divFuel fuel (n - d) d) (d * Succ (Nat.divFuel fuel (n - d) d)) n
    (Eq.sym (Nat.mulSucc d (Nat.divFuel fuel (n - d) d)))
    (Nat.leCongRight (d + d * Nat.divFuel fuel (n - d) d) (d + (n - d)) n (Nat.addSubCancel d n h)
      (Nat.leAddCong d (d * Nat.divFuel fuel (n - d) d) (n - d) (ih (n - d))))
Nat.divFuelLeStep fuel n d False h ih =
  Nat.leCongLeft 0 (d * 0) n (Eq.sym (Nat.mulZero d)) rfl

theorem Nat.divFuelLe : (fuel : Nat) -> (n : Nat) -> (d : Nat) -> d * Nat.divFuel fuel n d <= n
Nat.divFuelLe Zero n d = Nat.leCongLeft 0 (d * 0) n (Eq.sym (Nat.mulZero d)) rfl
Nat.divFuelLe (Succ fuel) n d = Nat.divFuelLeStep fuel n d (Nat.leq d n) rfl (\m -> Nat.divFuelLe fuel m d)

theorem Nat.fuelSub : (n : Nat) -> (d : Nat) -> (f : Nat) -> Not (d = 0) -> n <= Succ f -> n - d <= f
Nat.fuelSub n Zero f ok h = Void.exfalso (ok rfl)
Nat.fuelSub Zero (Succ d) f ok h = rfl
Nat.fuelSub (Succ n) (Succ d) f ok h = Nat.leTrans (n - d) n f (Nat.subLe n d) h

theorem Nat.divFuelBoundStep : (fuel : Nat) -> (n : Nat) -> (d : Nat) -> Not (d = 0) -> n <= Succ fuel -> (b : Bool) -> Nat.leq d n = b ->
    ((m : Nat) -> m <= fuel -> m < d * Succ (Nat.divFuel fuel m d)) ->
    n < d * Succ (if b then Succ (Nat.divFuel fuel (n - d) d) else 0)
Nat.divFuelBoundStep fuel n d ok hn True h ih =
  Nat.ltCongRight n (d + d * Succ (Nat.divFuel fuel (n - d) d)) (d * Succ (Succ (Nat.divFuel fuel (n - d) d)))
    (Eq.sym (Nat.mulSucc d (Succ (Nat.divFuel fuel (n - d) d))))
    (Nat.ltCongLeft (d + (n - d)) n (d + d * Succ (Nat.divFuel fuel (n - d) d)) (Nat.addSubCancel d n h)
      (Nat.ltAddCong d (n - d) (d * Succ (Nat.divFuel fuel (n - d) d)) (ih (n - d) (Nat.fuelSub n d fuel ok hn))))
Nat.divFuelBoundStep fuel n d ok hn False h ih =
  Nat.ltCongRight n d (d * 1) (Eq.sym (Nat.mulOne d)) (Nat.leqFalse d n h)

theorem Nat.nonzeroPos : (d : Nat) -> Not (d = 0) -> 0 < d
Nat.nonzeroPos Zero ok = Void.exfalso (ok rfl)
Nat.nonzeroPos (Succ d) ok = rfl

theorem Nat.divFuelBound : (fuel : Nat) -> (n : Nat) -> (d : Nat) -> Not (d = 0) -> n <= fuel -> n < d * Succ (Nat.divFuel fuel n d)
Nat.divFuelBound Zero Zero d ok hn = Nat.ltCongRight 0 d (d * 1) (Eq.sym (Nat.mulOne d)) (Nat.nonzeroPos d ok)
Nat.divFuelBound Zero (Succ n) d ok hn = Void.exfalso (Bool.falseNotTrue hn)
Nat.divFuelBound (Succ fuel) n d ok hn = Nat.divFuelBoundStep fuel n d ok hn (Nat.leq d n) rfl (\m hm -> Nat.divFuelBound fuel m d ok hm)


theorem Nat.divMod : (n : Nat) -> (d : Nat) -> (ok : d != 0) -> n = (n / d) * d + n % d
Nat.divMod n d ok = Eq.sym (Eq.trans (Eq.cong (\t -> t + (n - d * (n / d))) (Nat.mulComm (n / d) d)) (Nat.addSubCancel (d * (n / d)) n (Nat.divFuelLe n n d)))

theorem Nat.modLess : (n : Nat) -> (d : Nat) -> (ok : d != 0) -> n % d < d
Nat.modLess n d ok = Nat.subLtAdd n (d * (n / d)) d (Nat.divFuelLe n n d) (Nat.ltCongRight n (d * Succ (n / d)) (d + d * (n / d)) (Nat.mulSucc d (n / d)) (Nat.divFuelBound n n d ok (Nat.leRefl n)))

-- Division with remainder is unique: if `n = q * d + r` and `r < d`, then
-- `n / d = q` and `n % d = r`. Consequences for small numbers and for adding
-- `d`, and a few facts about subtraction.
theorem Nat.notBelowAdd : (d : Nat) -> (r : Nat) -> (m : Nat) -> r < d -> r = d + m -> Void
Nat.notBelowAdd d r m h e = Nat.lessIrrefl r (Nat.leTrans (Succ r) d r h (Nat.leCongRight d (d + m) r (Eq.sym e) (Nat.leAddRight d m)))

theorem Nat.quotUnique : (d : Nat) -> (q : Nat) -> (r : Nat) -> (q2 : Nat) -> (r2 : Nat) -> r < d -> r2 < d ->
    q * d + r = q2 * d + r2 -> q = q2
Nat.quotUnique d Zero     r Zero     r2 h1 h2 e = rfl
Nat.quotUnique d Zero     r (Succ k) r2 h1 h2 e = Void.exfalso (Nat.notBelowAdd d r (k * d + r2) h1 (Eq.trans e (Nat.addAssoc d (k * d) r2)))
Nat.quotUnique d (Succ a) r Zero     r2 h1 h2 e = Void.exfalso (Nat.notBelowAdd d r2 (a * d + r) h2 (Eq.trans (Eq.sym e) (Nat.addAssoc d (a * d) r)))
Nat.quotUnique d (Succ a) r (Succ b) r2 h1 h2 e =
  Eq.cong Succ (Nat.quotUnique d a r b r2 h1 h2
    (Nat.addCancelLeft d (a * d + r) (b * d + r2) (Eq.trans (Eq.sym (Nat.addAssoc d (a * d) r)) (Eq.trans e (Nat.addAssoc d (b * d) r2)))))

theorem Nat.divUnique : (n : Nat) -> (d : Nat) -> [auto ok : d != 0] -> (q : Nat) -> (r : Nat) -> r < d -> n = q * d + r -> n / d = q
Nat.divUnique n d q r h e = Nat.quotUnique d (n / d) (n % d) q r (Nat.modLess n d ok) h (Eq.trans (Eq.sym (Nat.divMod n d ok)) e)

theorem Nat.modUnique : (n : Nat) -> (d : Nat) -> [auto ok : d != 0] -> (q : Nat) -> (r : Nat) -> r < d -> n = q * d + r -> n % d = r
Nat.modUnique n d q r h e =
  Nat.addCancelLeft (q * d) (n % d) r
    (J (\y p -> y * d + n % d = q * d + r) (Eq.trans (Eq.sym (Nat.divMod n d ok)) e) (Nat.divUnique n d q r h e))

theorem Nat.modSmall : (n : Nat) -> (d : Nat) -> [auto ok : d != 0] -> n < d -> n % d = n
Nat.modSmall n d h = Nat.modUnique n d 0 n h rfl

theorem Nat.divSmall : (n : Nat) -> (d : Nat) -> [auto ok : d != 0] -> n < d -> n / d = 0
Nat.divSmall n d h = Nat.divUnique n d 0 n h rfl

theorem Nat.addDivModSelf : (d : Nat) -> (n : Nat) -> [auto ok : d != 0] -> d + n = Succ (n / d) * d + n % d
Nat.addDivModSelf d n = Eq.trans (Eq.cong (\t -> d + t) (Nat.divMod n d ok)) (Eq.sym (Nat.addAssoc d ((n / d) * d) (n % d)))

theorem Nat.addDivSelf : (d : Nat) -> (n : Nat) -> [auto ok : d != 0] -> (d + n) / d = Succ (n / d)
Nat.addDivSelf d n = Nat.divUnique (d + n) d (Succ (n / d)) (n % d) (Nat.modLess n d ok) (Nat.addDivModSelf d n)

theorem Nat.addModSelf : (d : Nat) -> (n : Nat) -> [auto ok : d != 0] -> (d + n) % d = n % d
Nat.addModSelf d n = Nat.modUnique (d + n) d (Succ (n / d)) (n % d) (Nat.modLess n d ok) (Nat.addDivModSelf d n)

theorem Nat.zeroSub : (n : Nat) -> 0 - n = 0
Nat.zeroSub Zero     = rfl
Nat.zeroSub (Succ n) = rfl

theorem Nat.subEqZero : (n : Nat) -> (m : Nat) -> n <= m -> n - m = 0
Nat.subEqZero Zero     m        h = Nat.zeroSub m
Nat.subEqZero (Succ n) Zero     h = Void.exfalso (Bool.falseNotTrue h)
Nat.subEqZero (Succ n) (Succ m) h = Nat.subEqZero n m h

theorem Nat.addOne : (a : Nat) -> a + 1 = Succ a
Nat.addOne a = Eq.trans (Nat.addSucc a 0) (Eq.cong Succ (Nat.addZero a))

theorem Nat.modLt : (n : Nat) -> (d : Nat) -> [auto ok : d != 0] -> n % d < d
Nat.modLt n d = Nat.modLess n d ok

theorem Nat.modSelf : (d : Nat) -> [auto ok : d != 0] -> d % d = 0
Nat.modSelf d = Nat.modUnique d d 1 0 (Nat.nonzeroPos d ok) (Eq.sym (Eq.trans (Nat.addZero (d + 0)) (Nat.addZero d)))

theorem Nat.divOne : (n : Nat) -> n / 1 = n
Nat.divOne n = Nat.divUnique n 1 n 0 rfl (Eq.sym (Eq.trans (Nat.addZero (n * 1)) (Nat.mulOne n)))

theorem Nat.succAddSub : (m : Nat) -> (r : Nat) -> Succ (m + r) - m = Succ r
Nat.succAddSub Zero     r = rfl
Nat.succAddSub (Succ m) r = Nat.succAddSub m r

theorem Nat.subSuccRight : (j : Nat) -> (t : Nat) -> Succ j <= t -> t - j = Succ (t - Succ j)
Nat.subSuccRight j        Zero     h = Void.exfalso (Bool.falseNotTrue h)
Nat.subSuccRight Zero     (Succ t) h = rfl
Nat.subSuccRight (Succ j) (Succ t) h = Nat.subSuccRight j t h

theorem Nat.succSub : (t : Nat) -> Succ t - t = 1
Nat.succSub Zero     = rfl
Nat.succSub (Succ t) = Nat.succSub t


-- Lists, continued

theorem List.lengthAppend : (xs : List a) -> (ys : List a) -> List.length (List.append xs ys) = List.length xs + List.length ys
List.lengthAppend Nil         ys = rfl
List.lengthAppend (Cons x xs) ys = Eq.cong Succ (List.lengthAppend xs ys)

List.IsNil : List a -> Prop
List.IsNil Nil         = Unit
List.IsNil (Cons x xs) = Void

theorem List.nilNotCons : (x : a) -> (xs : List a) -> Not (Nil = Cons x xs)
List.nilNotCons x xs p = J (\y q -> List.IsNil y) Trivial p

theorem List.consNotNil : (x : a) -> (xs : List a) -> Not (Cons x xs = Nil)
List.consNotNil x xs p = List.nilNotCons x xs (Eq.sym p)

List.headOr : a -> List a -> a
List.headOr d Nil         = d
List.headOr d (Cons x xs) = x

List.tailOf : List a -> List a
List.tailOf Nil         = Nil
List.tailOf (Cons x xs) = xs

List.decCons : (x : a) -> (y : a) -> (xs : List a) -> (ys : List a) ->
  Decidable (x = y) -> Decidable (xs = ys) -> Decidable (Cons x xs = Cons y ys)
List.decCons x y xs ys (Yes p) (Yes q) = Yes (J (\y' p' -> Cons x xs = Cons y' ys) (Eq.cong (Cons x) q) p)
List.decCons x y xs ys (No r)  dq      = No (\e -> r (Eq.cong (List.headOr x) e))
List.decCons x y xs ys (Yes p) (No r)  = No (\e -> r (Eq.cong List.tailOf e))

-- Equality of lists, from equality of their elements.
List.decEq : ((x : a) -> (y : a) -> Decidable (x = y)) -> (xs : List a) -> (ys : List a) -> Decidable (xs = ys)
List.decEq d Nil         Nil         = Yes rfl
List.decEq d Nil         (Cons y ys) = No (List.nilNotCons y ys)
List.decEq d (Cons x xs) Nil         = No (List.consNotNil x xs)
List.decEq d (Cons x xs) (Cons y ys) = List.decCons x y xs ys (d x y) (List.decEq d xs ys)

Pair.decMk : (x1 : a) -> (x2 : a) -> (y1 : b) -> (y2 : b) ->
  Decidable (x1 = x2) -> Decidable (y1 = y2) -> Decidable (MkPair x1 y1 = MkPair x2 y2)
Pair.decMk x1 x2 y1 y2 (Yes p) (Yes q) = Yes (J (\x' p' -> MkPair x1 y1 = MkPair x' y2) (Eq.cong (MkPair x1) q) p)
Pair.decMk x1 x2 y1 y2 (No r)  dq      = No (\e -> r (Eq.cong Pair.fst e))
Pair.decMk x1 x2 y1 y2 (Yes p) (No r)  = No (\e -> r (Eq.cong Pair.snd e))

-- Equality of pairs, from equality of their parts.
Pair.decEq : ((x : a) -> (y : a) -> Decidable (x = y)) -> ((x : b) -> (y : b) -> Decidable (x = y)) ->
  (p : Pair a b) -> (q : Pair a b) -> Decidable (p = q)
Pair.decEq da db (MkPair x1 y1) (MkPair x2 y2) = Pair.decMk x1 x2 y1 y2 (da x1 x2) (db y1 y2)

Maybe.IsNothing : Maybe a -> Prop
Maybe.IsNothing Nothing  = Unit
Maybe.IsNothing (Just x) = Void

theorem Maybe.nothingNotJust : (x : a) -> Not (Nothing = Just x)
Maybe.nothingNotJust x p = J (\y q -> Maybe.IsNothing y) Trivial p

theorem Maybe.justNotNothing : (x : a) -> Not (Just x = Nothing)
Maybe.justNotNothing x p = Maybe.nothingNotJust x (Eq.sym p)

-- The value, or `d` if there isn't one.
Maybe.withDefault : a -> Maybe a -> a
Maybe.withDefault d Nothing  = d
Maybe.withDefault d (Just x) = x

Maybe.decJust : (x : a) -> (y : a) -> Decidable (x = y) -> Decidable (Just x = Just y)
Maybe.decJust x y (Yes p) = Yes (Eq.cong Just p)
Maybe.decJust x y (No r)  = No (\e -> r (Eq.cong (Maybe.withDefault x) e))

-- Equality of optional values, from equality of the values.
Maybe.decEq : ((x : a) -> (y : a) -> Decidable (x = y)) -> (m : Maybe a) -> (n : Maybe a) -> Decidable (m = n)
Maybe.decEq d Nothing  Nothing  = Yes rfl
Maybe.decEq d Nothing  (Just y) = No (Maybe.nothingNotJust y)
Maybe.decEq d (Just x) Nothing  = No (Maybe.justNotNothing x)
Maybe.decEq d (Just x) (Just y) = Maybe.decJust x y (d x y)

-- Comparisons

type Ordering : Type =
  | Less
  | Equal
  | Greater

Nat.compare : Nat -> Nat -> Ordering
Nat.compare m n = if Nat.equal m n then Equal else (if Nat.leq m n then Less else Greater)

-- The first comparison, unless it's `Equal`.
Ordering.andThen : Ordering -> Ordering -> Ordering
Ordering.andThen Less    o = Less
Ordering.andThen Equal   o = o
Ordering.andThen Greater o = Greater

Ordering.isLess : Ordering -> Bool
Ordering.isLess Less    = True
Ordering.isLess Equal   = False
Ordering.isLess Greater = False

-- Number helpers.
Nat.min : Nat -> Nat -> Nat
Nat.min m n = if Nat.leq m n then m else n

Nat.max : Nat -> Nat -> Nat
Nat.max m n = if Nat.leq m n then n else m

-- The distance between two numbers; `(a - b) + (b - a)`, as one of them is 0.
Nat.absDiff : Nat -> Nat -> Nat
Nat.absDiff m n = (m - n) + (n - m)

-- `Nat.pow b e` is b to the power e.
Nat.pow : Nat -> Nat -> Nat
Nat.pow b Zero     = 1
Nat.pow b (Succ e) = b * Nat.pow b e

-- List toolkit. The callbacks are pure: the library has no convention yet for
-- callbacks with effects or `Partial`. Every function is structurally recursive.

List.map : (a -> b) -> List a -> List b
List.map f Nil         = Nil
List.map f (Cons x xs) = Cons (f x) (List.map f xs)

List.filter : (a -> Bool) -> List a -> List a
List.filter p Nil         = Nil
List.filter p (Cons x xs) = if p x then Cons x (List.filter p xs) else List.filter p xs

-- Left fold; tail-recursive. `List.foldl f z [x, y]` is `f (f z x) y`.
List.foldl : (b -> a -> b) -> b -> List a -> b
List.foldl f z Nil         = z
List.foldl f z (Cons x xs) = List.foldl f (f z x) xs

-- Running accumulations, the initial value first (Haskell's `scanl`):
-- `List.scanl f z [x, y]` is `[z, f z x, f (f z x) y]`. Always one longer than
-- the input.
List.scanl : (b -> a -> b) -> b -> List a -> List b
List.scanl f z Nil         = Cons z Nil
List.scanl f z (Cons x xs) = Cons z (List.scanl f (f z x) xs)

theorem List.scanlNil : List.scanl (\acc x -> acc + x) 5 Nil = [5]
List.scanlNil = rfl

theorem List.scanlSums : List.scanl (\acc x -> acc + x) 0 [1, 2, 3] = [0, 1, 3, 6]
List.scanlSums = rfl

-- Right fold. `List.foldr f z [x, y]` is `f x (f y z)`.
List.foldr : (a -> b -> b) -> b -> List a -> b
List.foldr f z Nil         = z
List.foldr f z (Cons x xs) = f x (List.foldr f z xs)

List.sum : List Nat -> Nat
List.sum xs = List.foldl Nat.add 0 xs

List.product : List Nat -> Nat
List.product xs = List.foldl Nat.mul 1 xs

List.maximum : List Nat -> Maybe Nat
List.maximum Nil         = Nothing
List.maximum (Cons x xs) = Just (List.foldl Nat.max x xs)

List.minimum : List Nat -> Maybe Nat
List.minimum Nil         = Nothing
List.minimum (Cons x xs) = Just (List.foldl Nat.min x xs)

-- Pairs up to the shorter list's length.
List.zip : List a -> List b -> List (Pair a b)
List.zip Nil         ys          = Nil
List.zip (Cons x xs) Nil         = Nil
List.zip (Cons x xs) (Cons y ys) = Cons (MkPair x y) (List.zip xs ys)

List.zipWith : (a -> b -> c) -> List a -> List b -> List c
List.zipWith f Nil         ys          = Nil
List.zipWith f (Cons x xs) Nil         = Nil
List.zipWith f (Cons x xs) (Cons y ys) = Cons (f x y) (List.zipWith f xs ys)

-- The first n elements (all of them if there are fewer).
List.take : Nat -> List a -> List a
List.take Zero     xs          = Nil
List.take (Succ n) Nil         = Nil
List.take (Succ n) (Cons x xs) = Cons x (List.take n xs)

-- All but the first n elements.
List.drop : Nat -> List a -> List a
List.drop Zero     xs          = xs
List.drop (Succ n) Nil         = Nil
List.drop (Succ n) (Cons x xs) = List.drop n xs

-- The element at index i, counting from 0.
List.get : List a -> Nat -> Maybe a
List.get Nil         i        = Nothing
List.get (Cons x xs) Zero     = Just x
List.get (Cons x xs) (Succ i) = List.get xs i

List.any : (a -> Bool) -> List a -> Bool
List.any p Nil         = False
List.any p (Cons x xs) = if p x then True else List.any p xs

List.all : (a -> Bool) -> List a -> Bool
List.all p Nil         = True
List.all p (Cons x xs) = if p x then List.all p xs else False

-- How many elements satisfy `p`.
List.count : (a -> Bool) -> List a -> Nat
List.count p xs = List.foldl (\n x -> if p x then Succ n else n) 0 xs

-- The first element satisfying `p`.
List.find : (a -> Bool) -> List a -> Maybe a
List.find p Nil         = Nothing
List.find p (Cons x xs) = if p x then Just x else List.find p xs

List.consJust : Maybe b -> List b -> List b
List.consJust Nothing  rest = rest
List.consJust (Just y) rest = Cons y rest

-- Keeps the `Just` results, in order.
List.mapMaybe : (a -> Maybe b) -> List a -> List b
List.mapMaybe f Nil         = Nil
List.mapMaybe f (Cons x xs) = List.consJust (f x) (List.mapMaybe f xs)

-- Joins a list of lists.
List.concat : List (List a) -> List a
List.concat Nil           = Nil
List.concat (Cons xs xss) = List.append xs (List.concat xss)

List.concatMap : (a -> List b) -> List a -> List b
List.concatMap f Nil         = Nil
List.concatMap f (Cons x xs) = List.append (f x) (List.concatMap f xs)

-- `List.replicate n x` is n copies of x.
List.replicate : Nat -> a -> List a
List.replicate Zero     x = Nil
List.replicate (Succ n) x = Cons x (List.replicate n x)

List.rangeFrom : Nat -> Nat -> List Nat
List.rangeFrom Zero     i = Nil
List.rangeFrom (Succ n) i = Cons i (List.rangeFrom n (Succ i))

-- `List.range n` is `[0, 1, ..., n - 1]`.
List.range : Nat -> List Nat
List.range n = List.rangeFrom n 0

List.reverse : List a -> List a
List.reverse xs = List.reverseOnto xs Nil

List.last : List a -> Maybe a
List.last Nil                  = Nothing
List.last (Cons x Nil)         = Just x
List.last (Cons x (Cons y ys)) = List.last (Cons y ys)

-- Membership, given a decision for equality (as `List.decEq` takes).
List.elem : ((x : a) -> (y : a) -> Decidable (x = y)) -> a -> List a -> Bool
List.elem d z Nil         = False
List.elem d z (Cons x xs) = if Decidable.toBool (d z x) then True else List.elem d z xs

-- The elements that satisfy `p`, and those that don't.
List.partition : (a -> Bool) -> List a -> Pair (List a) (List a)
List.partition p xs = MkPair (List.filter p xs) (List.filter (\x -> Bool.not (p x)) xs)

-- The value for the first pair whose key is equal, given a decision for equality.
List.lookup : ((x : k) -> (y : k) -> Decidable (x = y)) -> k -> List (Pair k v) -> Maybe v
List.lookup d key Nil                      = Nothing
List.lookup d key (Cons (MkPair k v) rest) = if Decidable.toBool (d key k) then Just v else List.lookup d key rest

-- Sorting

-- `Bool.inspect b motive t f` proves `motive b` by cases on `b`, remembering
-- which case it is. A proof about `if le x y then ... else ...` uses it with
-- `b = le x y` to get the branch's evidence (`le x y = True` or `= False`).
theorem Bool.inspect : (b : Bool) -> (motive : Bool -> Prop) -> (b = True -> motive True) -> (b = False -> motive False) -> motive b
Bool.inspect True  m t f = t rfl
Bool.inspect False m t f = f rfl

-- 1 for `True`, 0 for `False`.
Bool.toNat : Bool -> Nat
Bool.toNat False = 0
Bool.toNat True  = 1

theorem Nat.addRotate : (a : Nat) -> (b : Nat) -> (c : Nat) -> (a + b) + c = b + (a + c)
Nat.addRotate a b c = Eq.trans (Eq.cong (\t -> t + c) (Nat.addComm a b)) (Nat.addAssoc b a c)

theorem Nat.addLeftComm : (a : Nat) -> (b : Nat) -> (c : Nat) -> a + (b + c) = b + (a + c)
Nat.addLeftComm a b c = Eq.trans (Eq.sym (Nat.addAssoc a b c)) (Nat.addRotate a b c)

-- `<=` is total: if `m <= n` is false, then `n <= m`.
theorem Nat.leqTotal : (m : Nat) -> (n : Nat) -> Nat.leq m n = False -> Nat.leq n m = True
Nat.leqTotal m n h = Nat.lessLe n m (Nat.leqFalse m n h)

-- `True` for `Less` and `Equal`.
Ordering.isLessEq : Ordering -> Bool
Ordering.isLessEq Less    = True
Ordering.isLessEq Equal   = True
Ordering.isLessEq Greater = False

theorem Ordering.isLessEqIf : (d : Bool) -> Ordering.isLessEq (if d then Less else Greater) = d
Ordering.isLessEqIf True  = rfl
Ordering.isLessEqIf False = rfl

-- `Nat.compare` agrees with `<=`, so `List.sortBy` with it is total.
theorem Nat.compareLeq : (m : Nat) -> (n : Nat) -> Ordering.isLessEq (Nat.compare m n) = Nat.leq m n
Nat.compareLeq m n =
  Bool.inspect (Nat.equal m n)
    (\c -> Ordering.isLessEq (if c then Equal else (if Nat.leq m n then Less else Greater)) = Nat.leq m n)
    (\e -> Eq.sym (Nat.leCongRight m m n (Nat.equalSound m n e) (Nat.leRefl m)))
    (\e -> Ordering.isLessEqIf (Nat.leq m n))

theorem Nat.compareTotal : (m : Nat) -> (n : Nat) ->
  Ordering.isLessEq (Nat.compare m n) = False -> Ordering.isLessEq (Nat.compare n m) = True
Nat.compareTotal m n h = Eq.trans (Nat.compareLeq n m) (Nat.leqTotal m n (Eq.trans (Eq.sym (Nat.compareLeq m n)) h))

-- Merges two lists sorted by `le` ("may come before"), taking from the first
-- list on ties.
List.merge : (a -> a -> Bool) -> List a -> List a -> List a
List.merge le Nil         ys          = ys
List.merge le (Cons x xs) Nil         = Cons x xs
List.merge le (Cons x xs) (Cons y ys) =
  if le x y then Cons x (List.merge le xs (Cons y ys)) else Cons y (List.merge le (Cons x xs) ys)

-- Bottom-up merge sort, structurally recursive throughout. The runs are kept
-- like the digits of a binary counter: slot `i` is empty or holds a sorted run
-- of 2^i elements, newest first. Adding an element carries: two runs of the
-- same size merge into the next slot. Each element takes part in about log n
-- merges, so sorting is O(n log n).
List.pushRun : (a -> a -> Bool) -> List a -> List (Maybe (List a)) -> List (Maybe (List a))
List.pushRun le run Nil                  = Cons (Just run) Nil
List.pushRun le run (Cons Nothing rest)  = Cons (Just run) rest
List.pushRun le run (Cons (Just r) rest) = Cons Nothing (List.pushRun le (List.merge le r run) rest)

List.buildRuns : (a -> a -> Bool) -> List (Maybe (List a)) -> List a -> List (Maybe (List a))
List.buildRuns le c Nil         = c
List.buildRuns le c (Cons x xs) = List.buildRuns le (List.pushRun le (Cons x Nil) c) xs

-- Merges the runs, older (earlier) ones on the left.
List.mergeRuns : (a -> a -> Bool) -> List a -> List (Maybe (List a)) -> List a
List.mergeRuns le acc Nil                  = acc
List.mergeRuns le acc (Cons Nothing rest)  = List.mergeRuns le acc rest
List.mergeRuns le acc (Cons (Just r) rest) = List.mergeRuns le (List.merge le r acc) rest

-- Sorts by `le`, which says whether its first argument may come before its
-- second (`Nat.leq` for ascending numbers). Stable: equal elements keep their
-- order. `List.sortWithSorted` and `List.sortWithPerm` say it's correct.
List.sortWith : (a -> a -> Bool) -> List a -> List a
List.sortWith le xs = List.mergeRuns le Nil (List.buildRuns le Nil xs)

-- Sorts by a comparison, such as `Nat.compare` or `Text.compare`.
List.sortBy : (a -> a -> Ordering) -> List a -> List a
List.sortBy cmp xs = List.sortWith (\x y -> Ordering.isLessEq (cmp x y)) xs

-- Sorts numbers into ascending order.
List.sort : List Nat -> List Nat
List.sort xs = List.sortWith Nat.leq xs

-- `List.LeHead le z xs`: `z` may come before the first element of `xs`, if any.
List.LeHead : (a -> a -> Bool) -> a -> List a -> Prop
List.LeHead le z Nil         = Unit
List.LeHead le z (Cons y ys) = le z y = True

-- Each element may come before the next. For a transitive `le`, such as
-- `Nat.leq`, that orders every pair.
List.Sorted : (a -> a -> Bool) -> List a -> Prop
List.Sorted le Nil         = Unit
List.Sorted le (Cons x xs) = And (List.LeHead le x xs) (List.Sorted le xs)

-- The correctness proofs need only that `le` is total: `tot` below.
theorem List.mergeLeHead : (le : a -> a -> Bool) -> (z : a) -> (xs : List a) -> (ys : List a) ->
  List.LeHead le z xs -> List.LeHead le z ys -> List.LeHead le z (List.merge le xs ys)
List.mergeLeHead le z Nil         ys          hx hy = hy
List.mergeLeHead le z (Cons x xs) Nil         hx hy = hx
List.mergeLeHead le z (Cons x xs) (Cons y ys) hx hy =
  Bool.inspect (le x y)
    (\c -> List.LeHead le z (if c then Cons x (List.merge le xs (Cons y ys)) else Cons y (List.merge le (Cons x xs) ys)))
    (\e -> hx) (\e -> hy)

theorem List.mergeSorted : (le : a -> a -> Bool) -> ((x : a) -> (y : a) -> le x y = False -> le y x = True) ->
  (xs : List a) -> (ys : List a) -> List.Sorted le xs -> List.Sorted le ys -> List.Sorted le (List.merge le xs ys)
List.mergeSorted le tot Nil         ys          sx sy = sy
List.mergeSorted le tot (Cons x xs) Nil         sx sy = sx
List.mergeSorted le tot (Cons x xs) (Cons y ys) (Both hx sxs) (Both hy sys) =
  Bool.inspect (le x y)
    (\c -> List.Sorted le (if c then Cons x (List.merge le xs (Cons y ys)) else Cons y (List.merge le (Cons x xs) ys)))
    (\e -> Both (List.mergeLeHead le x xs (Cons y ys) hx e) (List.mergeSorted le tot xs (Cons y ys) sxs (Both hy sys)))
    (\e -> Both (List.mergeLeHead le y (Cons x xs) ys (tot x y e) hy) (List.mergeSorted le tot (Cons x xs) ys (Both hx sxs) sys))

-- Every run in the counter is sorted.
List.RunsSorted : (a -> a -> Bool) -> List (Maybe (List a)) -> Prop
List.RunsSorted le Nil                  = Unit
List.RunsSorted le (Cons Nothing rest)  = List.RunsSorted le rest
List.RunsSorted le (Cons (Just r) rest) = And (List.Sorted le r) (List.RunsSorted le rest)

theorem List.pushRunSorted : (le : a -> a -> Bool) -> ((x : a) -> (y : a) -> le x y = False -> le y x = True) ->
  (run : List a) -> (c : List (Maybe (List a))) -> List.Sorted le run -> List.RunsSorted le c -> List.RunsSorted le (List.pushRun le run c)
List.pushRunSorted le tot run Nil                  s h           = Both s Trivial
List.pushRunSorted le tot run (Cons Nothing rest)  s h           = Both s h
List.pushRunSorted le tot run (Cons (Just r) rest) s (Both sr h) =
  List.pushRunSorted le tot (List.merge le r run) rest (List.mergeSorted le tot r run sr s) h

theorem List.buildRunsSorted : (le : a -> a -> Bool) -> ((x : a) -> (y : a) -> le x y = False -> le y x = True) ->
  (c : List (Maybe (List a))) -> (xs : List a) -> List.RunsSorted le c -> List.RunsSorted le (List.buildRuns le c xs)
List.buildRunsSorted le tot c Nil         h = h
List.buildRunsSorted le tot c (Cons x xs) h =
  List.buildRunsSorted le tot (List.pushRun le (Cons x Nil) c) xs (List.pushRunSorted le tot (Cons x Nil) c (Both Trivial Trivial) h)

theorem List.mergeRunsSorted : (le : a -> a -> Bool) -> ((x : a) -> (y : a) -> le x y = False -> le y x = True) ->
  (acc : List a) -> (c : List (Maybe (List a))) -> List.Sorted le acc -> List.RunsSorted le c -> List.Sorted le (List.mergeRuns le acc c)
List.mergeRunsSorted le tot acc Nil                  s h           = s
List.mergeRunsSorted le tot acc (Cons Nothing rest)  s h           = List.mergeRunsSorted le tot acc rest s h
List.mergeRunsSorted le tot acc (Cons (Just r) rest) s (Both sr h) =
  List.mergeRunsSorted le tot (List.merge le r acc) rest (List.mergeSorted le tot r acc sr s) h

theorem List.sortWithSorted : (le : a -> a -> Bool) -> ((x : a) -> (y : a) -> le x y = False -> le y x = True) ->
  (xs : List a) -> List.Sorted le (List.sortWith le xs)
List.sortWithSorted le tot xs =
  List.mergeRunsSorted le tot Nil (List.buildRuns le Nil xs) Trivial (List.buildRunsSorted le tot Nil xs Trivial)

theorem List.sortBySorted : (cmp : a -> a -> Ordering) ->
  ((x : a) -> (y : a) -> Ordering.isLessEq (cmp x y) = False -> Ordering.isLessEq (cmp y x) = True) ->
  (xs : List a) -> List.Sorted (\x y -> Ordering.isLessEq (cmp x y)) (List.sortBy cmp xs)
List.sortBySorted cmp tot xs = List.sortWithSorted (\x y -> Ordering.isLessEq (cmp x y)) tot xs

theorem List.sortSorted : (xs : List Nat) -> List.Sorted Nat.leq (List.sort xs)
List.sortSorted xs = List.sortWithSorted Nat.leq Nat.leqTotal xs

-- How many elements satisfy `p` (as `List.count`, but recursing on the list,
-- which suits proofs).
List.occurrences : (a -> Bool) -> List a -> Nat
List.occurrences p Nil         = 0
List.occurrences p (Cons x xs) = Bool.toNat (p x) + List.occurrences p xs

-- `List.count` is `List.occurrences`, which suits proofs; counting and
-- `List.scanl` over `++`. (`List.drop 1` drops the starting value.)
theorem List.countStep : (b : Bool) -> (k : Nat) -> (o : Nat) -> (if b then Succ k else k) + o = k + (Bool.toNat b + o)
List.countStep True  k o = Eq.sym (Nat.addSucc k o)
List.countStep False k o = rfl

theorem List.countFold : (p : a -> Bool) -> (k : Nat) -> (xs : List a) ->
    List.foldl (\n x -> if p x then Succ n else n) k xs = k + List.occurrences p xs
List.countFold p k Nil         = Eq.sym (Nat.addZero k)
List.countFold p k (Cons x xs) = Eq.trans (List.countFold p (if p x then Succ k else k) xs) (List.countStep (p x) k (List.occurrences p xs))

theorem List.countOccurrences : (p : a -> Bool) -> (xs : List a) -> List.count p xs = List.occurrences p xs
List.countOccurrences p xs = List.countFold p 0 xs

theorem List.occurrencesAppend : (p : a -> Bool) -> (xs : List a) -> (ys : List a) ->
    List.occurrences p (List.append xs ys) = List.occurrences p xs + List.occurrences p ys
List.occurrencesAppend p Nil         ys = rfl
List.occurrencesAppend p (Cons x xs) ys =
  Eq.trans (Eq.cong (\t -> Bool.toNat (p x) + t) (List.occurrencesAppend p xs ys))
    (Eq.sym (Nat.addAssoc (Bool.toNat (p x)) (List.occurrences p xs) (List.occurrences p ys)))

theorem List.scanlCons : (f : b -> a -> b) -> (z : b) -> (xs : List a) -> List.scanl f z xs = Cons z (List.drop 1 (List.scanl f z xs))
List.scanlCons f z Nil         = rfl
List.scanlCons f z (Cons x xs) = rfl

theorem List.scanlAppend : (f : b -> a -> b) -> (z : b) -> (xs : List a) -> (ys : List a) ->
    List.drop 1 (List.scanl f z (List.append xs ys)) = List.append (List.drop 1 (List.scanl f z xs)) (List.drop 1 (List.scanl f (List.foldl f z xs) ys))
List.scanlAppend f z Nil         ys = rfl
List.scanlAppend f z (Cons x xs) ys =
  Eq.trans (List.scanlCons f (f z x) (List.append xs ys))
    (Eq.trans (Eq.cong (Cons (f z x)) (List.scanlAppend f (f z x) xs ys))
      (Eq.cong (\l -> List.append l (List.drop 1 (List.scanl f (List.foldl f (f z x) xs) ys))) (Eq.sym (List.scanlCons f (f z x) xs))))


-- `xs` and `ys` are permutations of each other: every test is passed by as
-- many elements of one as of the other. For elements with decidable equality
-- this is the usual meaning (test with `Nat.equal v` for each `v`). Counting
-- turns the proofs into arithmetic, and needs no equality on the elements.
List.Perm : List a -> List a -> Prop
List.Perm xs ys = (p : a -> Bool) -> List.occurrences p xs = List.occurrences p ys

theorem List.permRefl : (xs : List a) -> List.Perm xs xs
List.permRefl xs = \p -> rfl

theorem List.permSym : (xs : List a) -> (ys : List a) -> List.Perm xs ys -> List.Perm ys xs
List.permSym xs ys h = \p -> Eq.sym (h p)

theorem List.permTrans : (xs : List a) -> (ys : List a) -> (zs : List a) -> List.Perm xs ys -> List.Perm ys zs -> List.Perm xs zs
List.permTrans xs ys zs h1 h2 = \p -> Eq.trans (h1 p) (h2 p)

theorem List.occurrencesTrue : (xs : List a) -> List.occurrences (\x -> True) xs = List.length xs
List.occurrencesTrue Nil         = rfl
List.occurrencesTrue (Cons x xs) = Eq.cong Succ (List.occurrencesTrue xs)

theorem List.permLength : (xs : List a) -> (ys : List a) -> List.Perm xs ys -> List.length xs = List.length ys
List.permLength xs ys h = Eq.trans (Eq.sym (List.occurrencesTrue xs)) (Eq.trans (h (\x -> True)) (List.occurrencesTrue ys))

theorem List.mergeCount : (le : a -> a -> Bool) -> (p : a -> Bool) -> (xs : List a) -> (ys : List a) ->
  List.occurrences p (List.merge le xs ys) = List.occurrences p xs + List.occurrences p ys
List.mergeCount le p Nil         ys          = rfl
List.mergeCount le p (Cons x xs) Nil         = Eq.sym (Nat.addZero (List.occurrences p (Cons x xs)))
List.mergeCount le p (Cons x xs) (Cons y ys) =
  Bool.inspect (le x y)
    (\c -> List.occurrences p (if c then Cons x (List.merge le xs (Cons y ys)) else Cons y (List.merge le (Cons x xs) ys))
      = List.occurrences p (Cons x xs) + List.occurrences p (Cons y ys))
    (\e -> Eq.trans (Eq.cong (\t -> Bool.toNat (p x) + t) (List.mergeCount le p xs (Cons y ys)))
      (Eq.sym (Nat.addAssoc (Bool.toNat (p x)) (List.occurrences p xs) (List.occurrences p (Cons y ys)))))
    (\e -> Eq.trans (Eq.cong (\t -> Bool.toNat (p y) + t) (List.mergeCount le p (Cons x xs) ys))
      (Nat.addLeftComm (Bool.toNat (p y)) (List.occurrences p (Cons x xs)) (List.occurrences p ys)))

-- How many elements of all the runs satisfy `p`.
List.runsCount : (a -> Bool) -> List (Maybe (List a)) -> Nat
List.runsCount p Nil                  = 0
List.runsCount p (Cons Nothing rest)  = List.runsCount p rest
List.runsCount p (Cons (Just r) rest) = List.occurrences p r + List.runsCount p rest

theorem List.pushRunCount : (le : a -> a -> Bool) -> (p : a -> Bool) -> (run : List a) -> (c : List (Maybe (List a))) ->
  List.runsCount p (List.pushRun le run c) = List.occurrences p run + List.runsCount p c
List.pushRunCount le p run Nil                  = rfl
List.pushRunCount le p run (Cons Nothing rest)  = rfl
List.pushRunCount le p run (Cons (Just r) rest) =
  Eq.trans (List.pushRunCount le p (List.merge le r run) rest)
    (Eq.trans (Eq.cong (\t -> t + List.runsCount p rest) (List.mergeCount le p r run))
      (Nat.addRotate (List.occurrences p r) (List.occurrences p run) (List.runsCount p rest)))

theorem List.buildRunsCount : (le : a -> a -> Bool) -> (p : a -> Bool) -> (c : List (Maybe (List a))) -> (xs : List a) ->
  List.runsCount p (List.buildRuns le c xs) = List.runsCount p c + List.occurrences p xs
List.buildRunsCount le p c Nil         = Eq.sym (Nat.addZero (List.runsCount p c))
List.buildRunsCount le p c (Cons x xs) =
  Eq.trans (List.buildRunsCount le p (List.pushRun le (Cons x Nil) c) xs)
    (Eq.trans (Eq.cong (\t -> t + List.occurrences p xs) (List.pushRunCount le p (Cons x Nil) c))
      (Eq.trans (Eq.cong (\t -> (t + List.runsCount p c) + List.occurrences p xs) (Nat.addZero (Bool.toNat (p x))))
        (Nat.addRotate (Bool.toNat (p x)) (List.runsCount p c) (List.occurrences p xs))))

theorem List.mergeRunsCount : (le : a -> a -> Bool) -> (p : a -> Bool) -> (acc : List a) -> (c : List (Maybe (List a))) ->
  List.occurrences p (List.mergeRuns le acc c) = List.occurrences p acc + List.runsCount p c
List.mergeRunsCount le p acc Nil                  = Eq.sym (Nat.addZero (List.occurrences p acc))
List.mergeRunsCount le p acc (Cons Nothing rest)  = List.mergeRunsCount le p acc rest
List.mergeRunsCount le p acc (Cons (Just r) rest) =
  Eq.trans (List.mergeRunsCount le p (List.merge le r acc) rest)
    (Eq.trans (Eq.cong (\t -> t + List.runsCount p rest) (List.mergeCount le p r acc))
      (Nat.addRotate (List.occurrences p r) (List.occurrences p acc) (List.runsCount p rest)))

theorem List.sortWithPerm : (le : a -> a -> Bool) -> (xs : List a) -> List.Perm (List.sortWith le xs) xs
List.sortWithPerm le xs = \p ->
  Eq.trans (List.mergeRunsCount le p Nil (List.buildRuns le Nil xs)) (List.buildRunsCount le p Nil xs)

theorem List.sortByPerm : (cmp : a -> a -> Ordering) -> (xs : List a) -> List.Perm (List.sortBy cmp xs) xs
List.sortByPerm cmp xs = List.sortWithPerm (\x y -> Ordering.isLessEq (cmp x y)) xs

theorem List.sortPerm : (xs : List Nat) -> List.Perm (List.sort xs) xs
List.sortPerm xs = List.sortWithPerm Nat.leq xs

theorem List.sortLength : (xs : List Nat) -> List.length (List.sort xs) = List.length xs
List.sortLength xs = List.permLength (List.sort xs) xs (List.sortPerm xs)

-- Text (docs/proposals/text-and-io.md)

-- A sequence of Unicode scalar values. `"héllo"` is a `Text`. Equality and
-- ordering compare the sequence exactly, by scalar value, and length counts
-- scalar values; nothing is normalised, so `"\u{E9}"` and `"e\u{301}"` are
-- different texts. Code that goes through `Text.toList` and `Text.fromList`
-- and their lemmas, rather than `MkText`, won't depend on the representation.
type Text : Type =
  | MkText (chars : List Char)

Text.toList : Text -> List Char
Text.toList (MkText cs) = cs

Text.fromList : List Char -> Text
Text.fromList cs = MkText cs

theorem Text.toFromList : (cs : List Char) -> Text.toList (Text.fromList cs) = cs
Text.toFromList cs = rfl

theorem Text.fromToList : (t : Text) -> Text.fromList (Text.toList t) = t
Text.fromToList (MkText cs) = rfl

-- `a ++ b`
Text.append : Text -> Text -> Text
Text.append a b = MkText (List.append (Text.toList a) (Text.toList b))

-- The number of scalar values.
Text.length : Text -> Nat
Text.length t = List.length (Text.toList t)

theorem Text.lengthAppend : (a : Text) -> (b : Text) ->
  Text.length (Text.append a b) = Text.length a + Text.length b
Text.lengthAppend a b = List.lengthAppend (Text.toList a) (Text.toList b)

Text.isEmpty : Text -> Bool
Text.isEmpty (MkText Nil)         = True
Text.isEmpty (MkText (Cons c cs)) = False

Text.decEqFrom : (a : Text) -> (b : Text) -> Decidable (Text.toList a = Text.toList b) -> Decidable (a = b)
Text.decEqFrom a b (Yes p) = Yes (Eq.trans (Eq.sym (Text.fromToList a)) (Eq.trans (Eq.cong Text.fromList p) (Text.fromToList b)))
Text.decEqFrom a b (No r)  = No (\p -> r (Eq.cong Text.toList p))

Text.decEq : (a : Text) -> (b : Text) -> Decidable (a = b)
Text.decEq a b = Text.decEqFrom a b (List.decEq Char.decEq (Text.toList a) (Text.toList b))

-- The first character and the rest, unless the text is empty.
Text.uncons : Text -> Maybe (Pair Char Text)
Text.uncons (MkText Nil)         = Nothing
Text.uncons (MkText (Cons c cs)) = Just (MkPair c (MkText cs))

Text.foldChars : (Char -> b -> b) -> b -> List Char -> b
Text.foldChars f z Nil         = z
Text.foldChars f z (Cons c cs) = f c (Text.foldChars f z cs)

-- `Text.fold f z "abc"` is `f 'a' (f 'b' (f 'c' z))`.
Text.fold : (Char -> b -> b) -> b -> Text -> b
Text.fold f z t = Text.foldChars f z (Text.toList t)

Text.compareChars : List Char -> List Char -> Ordering
Text.compareChars Nil         Nil         = Equal
Text.compareChars Nil         (Cons y ys) = Less
Text.compareChars (Cons x xs) Nil         = Greater
Text.compareChars (Cons x xs) (Cons y ys) =
  Ordering.andThen (Nat.compare (Char.toNat x) (Char.toNat y)) (Text.compareChars xs ys)

-- Lexicographic, by scalar value. (Not JavaScript's order, which compares
-- UTF-16 code units: there, "\u{10000}" sorts before "\u{E000}".)
Text.compare : Text -> Text -> Ordering
Text.compare a b = Text.compareChars (Text.toList a) (Text.toList b)

Text.less : Text -> Text -> Bool
Text.less a b = Ordering.isLess (Text.compare a b)

-- Whitespace, for `Text.trim`: exactly space, tab, line feed, vertical tab,
-- form feed and carriage return. Not Unicode's `White_Space`.
Char.isSpaceCode : Nat -> Bool
Char.isSpaceCode 9  = True
Char.isSpaceCode 10 = True
Char.isSpaceCode 11 = True
Char.isSpaceCode 12 = True
Char.isSpaceCode 13 = True
Char.isSpaceCode 32 = True
Char.isSpaceCode _  = False

Char.isSpace : Char -> Bool
Char.isSpace c = Char.isSpaceCode (Char.toNat c)

Text.dropSpaces : List Char -> List Char
Text.dropSpaces Nil         = Nil
Text.dropSpaces (Cons c cs) = if Char.isSpace c then Text.dropSpaces cs else Cons c cs

-- Removes whitespace (as `Char.isSpace` defines it) from both ends.
Text.trim : Text -> Text
Text.trim t = MkText (List.reverseOnto (Text.dropSpaces (List.reverseOnto (Text.dropSpaces (Text.toList t)) Nil)) Nil)

-- Numbers as text

Nat.digitChar : Nat -> Char
Nat.digitChar 0 = '0'
Nat.digitChar 1 = '1'
Nat.digitChar 2 = '2'
Nat.digitChar 3 = '3'
Nat.digitChar 4 = '4'
Nat.digitChar 5 = '5'
Nat.digitChar 6 = '6'
Nat.digitChar 7 = '7'
Nat.digitChar 8 = '8'
Nat.digitChar _ = '9'

-- The digits of `n` in front of `acc`. `fuel` keeps it structurally
-- recursive; `n + 1` is always enough.
Nat.digitsOnto : Nat -> Nat -> List Char -> List Char
Nat.digitsOnto Zero        n acc = acc
Nat.digitsOnto (Succ fuel) n acc =
  if Nat.leq n 9 then Cons (Nat.digitChar n) acc else Nat.digitsOnto fuel (n / 10) (Cons (Nat.digitChar (n % 10)) acc)

-- Decimal, without leading zeros: `Nat.toText 42` is `"42"`.
Nat.toText : Nat -> Text
Nat.toText n = MkText (Nat.digitsOnto (Succ n) n Nil)

Maybe.andThen : Maybe a -> (a -> Maybe b) -> Maybe b
Maybe.andThen Nothing  f = Nothing
Maybe.andThen (Just x) f = f x

Maybe.map : (a -> b) -> Maybe a -> Maybe b
Maybe.map f Nothing  = Nothing
Maybe.map f (Just x) = Just (f x)

Char.digitValue : Char -> Maybe Nat
Char.digitValue c = if Nat.leq 48 (Char.toNat c) then (if Nat.leq (Char.toNat c) 57 then Just (Char.toNat c - 48) else Nothing) else Nothing

Text.readDigits : Nat -> List Char -> Maybe Nat
Text.readDigits acc Nil         = Just acc
Text.readDigits acc (Cons c cs) = Maybe.andThen (Char.digitValue c) (\d -> Text.readDigits (acc * 10 + d) cs)

-- A non-empty sequence of ASCII digits, and nothing else: no sign,
-- whitespace or separators. Leading zeros are allowed, so
-- `Text.toNat (Nat.toText n) = Just n` but `"007"` reads as 7.
Text.toNat : Text -> Maybe Nat
Text.toNat (MkText Nil)         = Nothing
Text.toNat (MkText (Cons c cs)) = Text.readDigits 0 (Cons c cs)

-- Integers (docs/proposals/integers.md)

-- An integer: `OfNat n` is `n`, and `NegSucc n` is `-(n + 1)`, so each
-- integer has exactly one form. The definitions compute through `Nat`'s, so
-- they're as compact as `Nat` is, and the kernel needs nothing new.
type Int : Type =
  | OfNat (n : Nat)
  | NegSucc (n : Nat)

Nat.toInt : Nat -> Int
Nat.toInt n = OfNat n

-- `-x`
Int.neg : Int -> Int
Int.neg (OfNat Zero)     = OfNat Zero
Int.neg (OfNat (Succ n)) = NegSucc n
Int.neg (NegSucc n)      = OfNat (Succ n)

-- `m - n` for naturals, as an integer. One subtraction decides which side
-- is bigger: `n - m` is zero exactly when `n <= m`.
Int.subNatNatFrom : Nat -> Nat -> Nat -> Int
Int.subNatNatFrom m n Zero     = OfNat (m - n)
Int.subNatNatFrom m n (Succ k) = NegSucc k

Int.subNatNat : Nat -> Nat -> Int
Int.subNatNat m n = Int.subNatNatFrom m n (n - m)

-- `a + b`
Int.add : Int -> Int -> Int
Int.add (OfNat m)   (OfNat n)   = OfNat (m + n)
Int.add (OfNat m)   (NegSucc n) = Int.subNatNat m (Succ n)
Int.add (NegSucc m) (OfNat n)   = Int.subNatNat n (Succ m)
Int.add (NegSucc m) (NegSucc n) = NegSucc (Succ (m + n))

-- `a - b`
Int.sub : Int -> Int -> Int
Int.sub a b = Int.add a (Int.neg b)

-- `a * b`. By constructors first, so `OfNat m * OfNat n` is `OfNat (m * n)`.
Int.mul : Int -> Int -> Int
Int.mul (OfNat m)   (OfNat n)   = OfNat (m * n)
Int.mul (OfNat m)   (NegSucc n) = Int.neg (OfNat (m * Succ n))
Int.mul (NegSucc m) (OfNat n)   = Int.neg (OfNat (Succ m * n))
Int.mul (NegSucc m) (NegSucc n) = OfNat (Succ m * Succ n)

-- `|x|`, as a `Nat`.
Int.natAbs : Int -> Nat
Int.natAbs (OfNat n)   = n
Int.natAbs (NegSucc n) = Succ n

-- `x` if it isn't negative, otherwise `0`.
Int.toNat : Int -> Nat
Int.toNat (OfNat n)   = n
Int.toNat (NegSucc n) = 0

-- The two constructors are different, and each is injective.

Int.IsOfNat : Int -> Prop
Int.IsOfNat (OfNat n)   = Unit
Int.IsOfNat (NegSucc n) = Void

theorem Int.ofNatNotNegSucc : (m : Nat) -> (n : Nat) -> Not (OfNat m = NegSucc n)
Int.ofNatNotNegSucc m n p = J (\y q -> Int.IsOfNat y) Trivial p

theorem Int.negSuccNotOfNat : (m : Nat) -> (n : Nat) -> Not (NegSucc m = OfNat n)
Int.negSuccNotOfNat m n p = Int.ofNatNotNegSucc n m (Eq.sym p)

theorem Int.ofNatInjective : (m : Nat) -> (n : Nat) -> OfNat m = OfNat n -> m = n
Int.ofNatInjective m n p = Eq.cong Int.toNat p

theorem Int.negSuccInjective : (m : Nat) -> (n : Nat) -> NegSucc m = NegSucc n -> m = n
Int.negSuccInjective m n p = Nat.succInjective m n (Eq.cong Int.natAbs p)

Int.decOfNat : (m : Nat) -> (n : Nat) -> Decidable (m = n) -> Decidable (OfNat m = OfNat n)
Int.decOfNat m n (Yes p) = Yes (Eq.cong OfNat p)
Int.decOfNat m n (No r)  = No (\p -> r (Int.ofNatInjective m n p))

Int.decNegSucc : (m : Nat) -> (n : Nat) -> Decidable (m = n) -> Decidable (NegSucc m = NegSucc n)
Int.decNegSucc m n (Yes p) = Yes (Eq.cong NegSucc p)
Int.decNegSucc m n (No r)  = No (\p -> r (Int.negSuccInjective m n p))

-- For two integers this computes `Yes rfl` or a `No` of constant size,
-- however big they are, since `Nat.decEq` does.
Int.decEq : (a : Int) -> (b : Int) -> Decidable (a = b)
Int.decEq (OfNat m)   (OfNat n)   = Int.decOfNat m n (Nat.decEq m n)
Int.decEq (OfNat m)   (NegSucc n) = No (Int.ofNatNotNegSucc m n)
Int.decEq (NegSucc m) (OfNat n)   = No (Int.negSuccNotOfNat m n)
Int.decEq (NegSucc m) (NegSucc n) = Int.decNegSucc m n (Nat.decEq m n)

-- `a <= b`. Every negative is below every non-negative; among negatives the
-- order flips, since `NegSucc n` is `-(n+1)`.
Int.leq : Int -> Int -> Bool
Int.leq (OfNat m)   (OfNat n)   = Nat.leq m n
Int.leq (OfNat m)   (NegSucc n) = False
Int.leq (NegSucc m) (OfNat n)   = True
Int.leq (NegSucc m) (NegSucc n) = Nat.leq n m

-- `a < b`
Int.less : Int -> Int -> Bool
Int.less (OfNat m)   (OfNat n)   = Nat.leq (Succ m) n
Int.less (OfNat m)   (NegSucc n) = False
Int.less (NegSucc m) (OfNat n)   = True
Int.less (NegSucc m) (NegSucc n) = Nat.leq (Succ n) m

Int.LessEq : Int -> Int -> Prop
Int.LessEq a b = Int.leq a b = True

Int.LessThan : Int -> Int -> Prop
Int.LessThan a b = Int.less a b = True

Int.decLessEq : (a : Int) -> (b : Int) -> Decidable (Int.LessEq a b)
Int.decLessEq a b = Bool.decTrue (Int.leq a b)

Int.decLessThan : (a : Int) -> (b : Int) -> Decidable (Int.LessThan a b)
Int.decLessThan a b = Bool.decTrue (Int.less a b)

Int.compare : Int -> Int -> Ordering
Int.compare (OfNat m)   (OfNat n)   = Nat.compare m n
Int.compare (OfNat m)   (NegSucc n) = Greater
Int.compare (NegSucc m) (OfNat n)   = Less
Int.compare (NegSucc m) (NegSucc n) = Nat.compare n m

-- `|x|`, as an `Int`.
Int.abs : Int -> Int
Int.abs (OfNat n)   = OfNat n
Int.abs (NegSucc n) = OfNat (Succ n)

-- `Just x` if `x` isn't negative, otherwise `Nothing`.
Int.toNatChecked : Int -> Maybe Nat
Int.toNatChecked (OfNat n)   = Just n
Int.toNatChecked (NegSucc n) = Nothing

-- `-1`, `0` or `1`.
Int.sign : Int -> Int
Int.sign (OfNat Zero)     = OfNat Zero
Int.sign (OfNat (Succ n)) = OfNat 1
Int.sign (NegSucc n)      = NegSucc 0

-- Decimal, with a `-` in front of a negative: `"-42"`. Never `"-0"`.
Int.toText : Int -> Text
Int.toText (OfNat n)   = Nat.toText n
Int.toText (NegSucc n) = MkText (Cons '-' (Text.toList (Nat.toText (Succ n))))

-- An optional `-`, then one or more ASCII digits, and nothing else. Leading
-- zeros are fine and `"-0"` is `0`; `"-"`, `""` and `"+5"` are `Nothing`.
Text.toInt : Text -> Maybe Int
Text.toInt (MkText Nil)         = Nothing
Text.toInt (MkText (Cons c cs)) =
  if Nat.equal (Char.toNat c) 45
  then Maybe.map (\n -> Int.neg (OfNat n)) (Text.toNat (MkText cs))
  else Maybe.map OfNat (Text.toNat (MkText (Cons c cs)))

-- Division. `a / d` and `a % d` are Euclidean: `a = d * (a / d) + a % d`
-- with `0 <= a % d < |d|`, whatever the signs, so `-18 % 100` is `82`.
-- Each case divides naturals by a `Succ n`, which `auto` sees isn't zero.
-- The divisor can't be zero, but the case still has to be covered: `ok`
-- rules it out.
Int.div : (a : Int) -> (d : Int) -> [auto ok : d != OfNat 0] -> Int
Int.div a           (OfNat Zero)     = Void.absurd (ok rfl)
Int.div (OfNat m)   (OfNat (Succ n)) = OfNat (m / Succ n)
Int.div (NegSucc m) (OfNat (Succ n)) = NegSucc (m / Succ n)
Int.div (OfNat m)   (NegSucc n)      = Int.neg (OfNat (m / Succ n))
Int.div (NegSucc m) (NegSucc n)      = OfNat (Succ (m / Succ n))

-- Never negative. For `NegSucc m`, `m % Succ n <= n`, so the subtraction
-- doesn't stop at zero.
Int.mod : (a : Int) -> (d : Int) -> [auto ok : d != OfNat 0] -> Int
Int.mod a           (OfNat Zero)     = Void.absurd (ok rfl)
Int.mod (OfNat m)   (OfNat (Succ n)) = OfNat (m % Succ n)
Int.mod (NegSucc m) (OfNat (Succ n)) = OfNat (n - m % Succ n)
Int.mod (OfNat m)   (NegSucc n)      = OfNat (m % Succ n)
Int.mod (NegSucc m) (NegSucc n)      = OfNat (n - m % Succ n)

-- `x % d` as a `Nat`, for indexing: `(x.modNat d).toInt = x % d.toInt`.
Int.modNat : Int -> (d : Nat) -> [auto ok : d != 0] -> Nat
Int.modNat x           Zero     = Void.absurd (ok rfl)
Int.modNat (OfNat m)   (Succ n) = m % Succ n
Int.modNat (NegSucc m) (Succ n) = n - m % Succ n

-- Truncating division, rounding toward zero; the remainder has the
-- dividend's sign (C, Rust's `/` and `%`, JavaScript's `BigInt`).
Int.tdiv : (a : Int) -> (d : Int) -> [auto ok : d != OfNat 0] -> Int
Int.tdiv a           (OfNat Zero)     = Void.absurd (ok rfl)
Int.tdiv (OfNat m)   (OfNat (Succ n)) = OfNat (m / Succ n)
Int.tdiv (NegSucc m) (OfNat (Succ n)) = Int.neg (OfNat (Succ m / Succ n))
Int.tdiv (OfNat m)   (NegSucc n)      = Int.neg (OfNat (m / Succ n))
Int.tdiv (NegSucc m) (NegSucc n)      = OfNat (Succ m / Succ n)

Int.tmod : (a : Int) -> (d : Int) -> [auto ok : d != OfNat 0] -> Int
Int.tmod a           (OfNat Zero)     = Void.absurd (ok rfl)
Int.tmod (OfNat m)   (OfNat (Succ n)) = OfNat (m % Succ n)
Int.tmod (NegSucc m) (OfNat (Succ n)) = Int.neg (OfNat (Succ m % Succ n))
Int.tmod (OfNat m)   (NegSucc n)      = OfNat (m % Succ n)
Int.tmod (NegSucc m) (NegSucc n)      = Int.neg (OfNat (Succ m % Succ n))

-- Flooring division, rounding toward negative infinity; the remainder has
-- the divisor's sign (Python, Haskell's `div` and `mod`). The same as
-- Euclidean division when the divisor is positive.
Int.fdiv : (a : Int) -> (d : Int) -> [auto ok : d != OfNat 0] -> Int
Int.fdiv a                  (OfNat Zero)     = Void.absurd (ok rfl)
Int.fdiv (OfNat m)          (OfNat (Succ n)) = OfNat (m / Succ n)
Int.fdiv (NegSucc m)        (OfNat (Succ n)) = NegSucc (m / Succ n)
Int.fdiv (OfNat Zero)       (NegSucc n)      = OfNat Zero
Int.fdiv (OfNat (Succ m))   (NegSucc n)      = NegSucc (m / Succ n)
Int.fdiv (NegSucc m)        (NegSucc n)      = OfNat (Succ m / Succ n)

Int.fmod : (a : Int) -> (d : Int) -> [auto ok : d != OfNat 0] -> Int
Int.fmod a                  (OfNat Zero)     = Void.absurd (ok rfl)
Int.fmod (OfNat m)          (OfNat (Succ n)) = OfNat (m % Succ n)
Int.fmod (NegSucc m)        (OfNat (Succ n)) = OfNat (n - m % Succ n)
Int.fmod (OfNat Zero)       (NegSucc n)      = OfNat Zero
Int.fmod (OfNat (Succ m))   (NegSucc n)      = Int.neg (OfNat (n - m % Succ n))
Int.fmod (NegSucc m)        (NegSucc n)      = Int.neg (OfNat (Succ m % Succ n))

-- Lemmas (checkpoint 1)

theorem Int.toNatCheckedToInt : (n : Nat) -> Int.toNatChecked (Nat.toInt n) = Just n
Int.toNatCheckedToInt n = rfl

theorem Int.negNeg : (x : Int) -> Int.neg (Int.neg x) = x
Int.negNeg (OfNat Zero)     = rfl
Int.negNeg (OfNat (Succ n)) = rfl
Int.negNeg (NegSucc n)      = rfl

-- These hold by computation; stating them keeps it that way.
theorem Int.toIntAdd : (m : Nat) -> (n : Nat) -> Nat.toInt (m + n) = Int.add (Nat.toInt m) (Nat.toInt n)
Int.toIntAdd m n = rfl

theorem Int.toIntMul : (m : Nat) -> (n : Nat) -> Nat.toInt (m * n) = Int.mul (Nat.toInt m) (Nat.toInt n)
Int.toIntMul m n = rfl

theorem Int.toNatToInt : (n : Nat) -> Int.toNat (Nat.toInt n) = n
Int.toNatToInt n = rfl

theorem Int.natAbsToInt : (n : Nat) -> Int.natAbs (Nat.toInt n) = n
Int.natAbsToInt n = rfl

theorem Int.natAbsNeg : (x : Int) -> Int.natAbs (Int.neg x) = Int.natAbs x
Int.natAbsNeg (OfNat Zero)     = rfl
Int.natAbsNeg (OfNat (Succ n)) = rfl
Int.natAbsNeg (NegSucc n)      = rfl

-- Lemmas (checkpoint 2): division.
--
-- The divisor's proof is an `auto` argument, so at a use such as
-- `Int.divAddMod x 7` it's found the same way as in `x / 7`, and the two
-- terms match: a stuck `x % 7` keeps its proof in it.

theorem Nat.toIntNeZero : (d : Nat) -> d != 0 -> Nat.toInt d != 0
Nat.toIntNeZero d ok p = ok (Int.ofNatInjective d 0 p)

-- `x.modNat d < d`; `Int.modNatLt x 100` is the dial's `x.modNat 100 < 100`.
theorem Int.modNatLt : (x : Int) -> (d : Nat) -> [auto ok : d != 0] -> Int.modNat x d < d
Int.modNatLt x           Zero     = Void.exfalso (ok rfl)
Int.modNatLt (OfNat m)   (Succ n) = Nat.modLess m (Succ n) (Nat.succNotZero n)
Int.modNatLt (NegSucc m) (Succ n) = Nat.subLe n (m % Succ n)

-- For a variable `d`, pass `[ok2 := Nat.toIntNeZero d ok]`.
theorem Int.modNatToInt : (x : Int) -> (d : Nat) -> [auto ok : d != 0] -> [auto ok2 : Nat.toInt d != 0] ->
    Nat.toInt (Int.modNat x d) = x % Nat.toInt d
Int.modNatToInt x           Zero     = Void.exfalso (ok rfl)
Int.modNatToInt (OfNat m)   (Succ n) = rfl
Int.modNatToInt (NegSucc m) (Succ n) = rfl

theorem Int.toIntDiv : (n : Nat) -> (d : Nat) -> [auto ok : d != 0] -> [auto ok2 : Nat.toInt d != 0] ->
    Nat.toInt (n / d) = Nat.toInt n / Nat.toInt d
Int.toIntDiv n Zero     = Void.exfalso (ok rfl)
Int.toIntDiv n (Succ d) = rfl

theorem Int.toIntMod : (n : Nat) -> (d : Nat) -> [auto ok : d != 0] -> [auto ok2 : Nat.toInt d != 0] ->
    Nat.toInt (n % d) = Nat.toInt n % Nat.toInt d
Int.toIntMod n Zero     = Void.exfalso (ok rfl)
Int.toIntMod n (Succ d) = rfl

-- Remainder bounds: `0 <= a % d < |d|`.
theorem Int.modNonneg : (a : Int) -> (d : Int) -> [auto ok : d != 0] -> 0 <= a % d
Int.modNonneg a           (OfNat Zero)     = Void.exfalso (ok rfl)
Int.modNonneg (OfNat m)   (OfNat (Succ n)) = rfl
Int.modNonneg (NegSucc m) (OfNat (Succ n)) = rfl
Int.modNonneg (OfNat m)   (NegSucc n)      = rfl
Int.modNonneg (NegSucc m) (NegSucc n)      = rfl

theorem Int.modLtAbs : (a : Int) -> (d : Int) -> [auto ok : d != 0] -> a % d < Nat.toInt (Int.natAbs d)
Int.modLtAbs a           (OfNat Zero)     = Void.exfalso (ok rfl)
Int.modLtAbs (OfNat m)   (OfNat (Succ n)) = Nat.modLess m (Succ n) (Nat.succNotZero n)
Int.modLtAbs (NegSucc m) (OfNat (Succ n)) = Nat.subLe n (m % Succ n)
Int.modLtAbs (OfNat m)   (NegSucc n)      = Nat.modLess m (Succ n) (Nat.succNotZero n)
Int.modLtAbs (NegSucc m) (NegSucc n)      = Nat.subLe n (m % Succ n)

-- The division law's negative-dividend cases. With `q = m / Succ n` and
-- `r = m % Succ n`, `d * (a / d)` computes to `NegSucc (q + n * Succ q)`,
-- and adding `n - r` gives `-(m + 1)`: `Succ (q + n * Succ q) - (n - r)`
-- is `Succ m`, because `q + n * Succ q = m + (n - r)`.
theorem Int.divAddModNeg : (m : Nat) -> (n : Nat) -> (q : Nat) -> (r : Nat) -> m = q * Succ n + r -> r <= n ->
    Int.add (NegSucc (q + n * Succ q)) (OfNat (n - r)) = NegSucc m
Int.divAddModNeg m n q r h hr =
  Eq.cong (Int.subNatNatFrom (n - r) (Succ (q + n * Succ q)))
    (Eq.trans
      (Eq.cong (\t -> Succ t - (n - r))
        (Eq.sym
          (Eq.trans (Eq.cong (\t -> t + (n - r)) h)
          (Eq.trans (Nat.addAssoc (q * Succ n) r (n - r))
          (Eq.trans (Eq.cong (\t -> q * Succ n + t) (Nat.addSubCancel r n hr))
          (Eq.trans (Eq.cong (\t -> t + n) (Nat.mulComm q (Succ n)))
          (Eq.trans (Nat.addAssoc q (n * q) n)
          (Eq.trans (Eq.cong (\t -> q + t) (Nat.addComm (n * q) n))
                    (Eq.cong (\t -> q + t) (Eq.sym (Nat.mulSucc n q)))))))))))
      (Nat.addSub (Succ m) (n - r)))

-- The non-negative dividend, negative divisor case: `Int.neg (OfNat q)`
-- only computes once `q` is split.
theorem Int.divAddModPosNeg : (m : Nat) -> (n : Nat) -> (q : Nat) -> (r : Nat) -> m = q * Succ n + r ->
    Int.add (Int.mul (NegSucc n) (Int.neg (OfNat q))) (OfNat r) = OfNat m
Int.divAddModPosNeg m n Zero r h =
  Eq.trans (Eq.cong (\t -> Int.add (Int.neg (OfNat t)) (OfNat r)) (Nat.mulZero n)) (Eq.cong OfNat (Eq.sym h))
Int.divAddModPosNeg m n (Succ q) r h =
  Eq.cong OfNat (Eq.trans (Eq.cong (\t -> t + r) (Nat.mulComm (Succ n) (Succ q))) (Eq.sym h))

-- The division law.
theorem Int.divAddMod : (a : Int) -> (d : Int) -> [auto ok : d != 0] -> d * (a / d) + a % d = a
Int.divAddMod a           (OfNat Zero)     = Void.exfalso (ok rfl)
Int.divAddMod (OfNat m)   (OfNat (Succ n)) =
  Eq.cong OfNat (Eq.trans (Eq.cong (\t -> t + m % Succ n) (Nat.mulComm (Succ n) (m / Succ n)))
    (Eq.sym (Nat.divMod m (Succ n) (Nat.succNotZero n))))
Int.divAddMod (NegSucc m) (OfNat (Succ n)) =
  Int.divAddModNeg m n (m / Succ n) (m % Succ n) (Nat.divMod m (Succ n) (Nat.succNotZero n))
    (Nat.modLess m (Succ n) (Nat.succNotZero n))
Int.divAddMod (OfNat m)   (NegSucc n)      =
  Int.divAddModPosNeg m n (m / Succ n) (m % Succ n) (Nat.divMod m (Succ n) (Nat.succNotZero n))
Int.divAddMod (NegSucc m) (NegSucc n)      =
  Int.divAddModNeg m n (m / Succ n) (m % Succ n) (Nat.divMod m (Succ n) (Nat.succNotZero n))
    (Nat.modLess m (Succ n) (Nat.succNotZero n))

-- Splitting and joining

-- `Text.splitChars s cs` is the first field and the rest: never empty.
Text.splitCons : Char -> Char -> Bool -> Pair (List Char) (List (List Char)) -> Pair (List Char) (List (List Char))
Text.splitCons s c True  (MkPair f fs) = MkPair Nil (Cons f fs)
Text.splitCons s c False (MkPair f fs) = MkPair (Cons c f) fs

Text.splitChars : Char -> List Char -> Pair (List Char) (List (List Char))
Text.splitChars s Nil         = MkPair Nil Nil
Text.splitChars s (Cons c cs) = Text.splitCons s c (Decidable.toBool (Char.decEq c s)) (Text.splitChars s cs)

Text.joinChars : Char -> List Char -> List (List Char) -> List Char
Text.joinChars s f Nil         = f
Text.joinChars s f (Cons g gs) = List.append f (Cons s (Text.joinChars s g gs))

Text.joinPair : Char -> Pair (List Char) (List (List Char)) -> List Char
Text.joinPair s (MkPair f fs) = Text.joinChars s f fs

theorem Text.joinCons : (s : Char) -> (c : Char) -> (f : List Char) -> (fs : List (List Char)) ->
  Text.joinChars s (Cons c f) fs = Cons c (Text.joinChars s f fs)
Text.joinCons s c f Nil         = rfl
Text.joinCons s c f (Cons g gs) = rfl

theorem Text.joinSplitCons : (s : Char) -> (c : Char) -> (cs : List Char) ->
  (p : Pair (List Char) (List (List Char))) -> Text.joinPair s p = cs ->
  (d : Decidable (c = s)) -> Text.joinPair s (Text.splitCons s c (Decidable.toBool d) p) = Cons c cs
Text.joinSplitCons s c cs (MkPair f fs) h (Yes e) =
  Eq.trans (Eq.cong (Cons s) h) (Eq.cong (\x -> Cons x cs) (Eq.sym e))
Text.joinSplitCons s c cs (MkPair f fs) h (No r) =
  Eq.trans (Text.joinCons s c f fs) (Eq.cong (Cons c) h)

theorem Text.joinSplitChars : (s : Char) -> (cs : List Char) -> Text.joinPair s (Text.splitChars s cs) = cs
Text.joinSplitChars s Nil         = rfl
Text.joinSplitChars s (Cons c cs) =
  Text.joinSplitCons s c cs (Text.splitChars s cs) (Text.joinSplitChars s cs) (Char.decEq c s)

Text.textsOf : List (List Char) -> List Text
Text.textsOf Nil         = Nil
Text.textsOf (Cons f fs) = Cons (MkText f) (Text.textsOf fs)

Text.charListsOf : List Text -> List (List Char)
Text.charListsOf Nil         = Nil
Text.charListsOf (Cons t ts) = Cons (Text.toList t) (Text.charListsOf ts)

theorem Text.charListsOfTexts : (fs : List (List Char)) -> Text.charListsOf (Text.textsOf fs) = fs
Text.charListsOfTexts Nil         = rfl
Text.charListsOfTexts (Cons f fs) = Eq.cong (Cons f) (Text.charListsOfTexts fs)

Text.splitTexts : Pair (List Char) (List (List Char)) -> List Text
Text.splitTexts (MkPair f fs) = Cons (MkText f) (Text.textsOf fs)

-- The fields between separators, keeping empty ones: splitting "a,,b" on
-- ',' gives ["a", "", "b"], and splitting "" gives [""].
Text.split : Char -> Text -> List Text
Text.split s t = Text.splitTexts (Text.splitChars s (Text.toList t))

-- The texts with `s` between them. `Text.join s (Text.split s t) = t`.
Text.join : Char -> List Text -> Text
Text.join s Nil         = MkText Nil
Text.join s (Cons t ts) = MkText (Text.joinChars s (Text.toList t) (Text.charListsOf ts))

theorem Text.joinSplitTexts : (s : Char) -> (p : Pair (List Char) (List (List Char))) ->
  Text.join s (Text.splitTexts p) = MkText (Text.joinPair s p)
Text.joinSplitTexts s (MkPair f fs) = Eq.cong (\l -> MkText (Text.joinChars s f l)) (Text.charListsOfTexts fs)

theorem Text.joinSplit : (s : Char) -> (t : Text) -> Text.join s (Text.split s t) = t
Text.joinSplit s (MkText cs) =
  Eq.trans (Text.joinSplitTexts s (Text.splitChars s cs)) (Eq.cong MkText (Text.joinSplitChars s cs))

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
Effect.foldComp : [op : Type] -> [res : op -> Type] -> [a r : Type] ->
  (a -> r) -> ((o : op) -> (res o -> r) -> r) -> Comp op res a -> r
Effect.foldComp done call (Done x)      = done x
Effect.foldComp done call (Call o rest) = call o (\y -> foldComp done call (rest y))

-- Sequencing: run `c`, then `next` with its result.
Effect.bind : [op : Type] -> [res : op -> Type] -> [a b : Type] ->
  Comp op res a -> (a -> Comp op res b) -> Comp op res b
Effect.bind (Done x)      next = next x
Effect.bind (Call o rest) next = Call o (\y -> bind (rest y) next)

-- Rows: signatures side by side, and mappings between signatures.

-- The operations of two signatures: the row `{l, r}`.
type Effect.Plus (l : Type) (r : Type) : Type =
  | L (o : l)
  | R (o : r)

Effect.PlusRes : [l r : Type] -> (l -> Type) -> (r -> Type) -> Plus l r -> Type
Effect.PlusRes lres rres (L o) = lres o
Effect.PlusRes lres rres (R o) = rres o

-- A mapping from one signature into another. Because what an operation
-- returns depends on the operation, a mapping says both where each
-- operation goes and how its response comes back.
type Effect.SigMap (op1 : Type) (res1 : op1 -> Type) (op2 : Type) (res2 : op2 -> Type) : Type =
  | MkSigMap (inject : op1 -> op2) (reply : (o : op1) -> res2 (inject o) -> res1 o)

Effect.sigInject : [op1 : Type] -> [res1 : op1 -> Type] -> [op2 : Type] -> [res2 : op2 -> Type] ->
  SigMap op1 res1 op2 res2 -> op1 -> op2
Effect.sigInject (MkSigMap inj rep) o = inj o

Effect.sigReply : [op1 : Type] -> [res1 : op1 -> Type] -> [op2 : Type] -> [res2 : op2 -> Type] ->
  (m : SigMap op1 res1 op2 res2) -> (o : op1) -> res2 (sigInject m o) -> res1 o
Effect.sigReply (MkSigMap inj rep) o r = rep o r

-- Moves a computation along a mapping. Operations stay in the same order;
-- only their names in the signature change.
Effect.translate : [op1 : Type] -> [res1 : op1 -> Type] -> [op2 : Type] -> [res2 : op2 -> Type] -> [a : Type] ->
  SigMap op1 res1 op2 res2 -> Comp op1 res1 a -> Comp op2 res2 a
Effect.translate m (Done x)      = Done x
Effect.translate m (Call o rest) = Call (sigInject m o) (\r -> translate m (rest (sigReply m o r)))

Effect.sigId : [op : Type] -> [res : op -> Type] -> SigMap op res op res
Effect.sigId = MkSigMap (\o -> o) (\o r -> r)

Effect.sigCompose : [op1 : Type] -> [res1 : op1 -> Type] -> [op2 : Type] -> [res2 : op2 -> Type] ->
  [op3 : Type] -> [res3 : op3 -> Type] ->
  SigMap op1 res1 op2 res2 -> SigMap op2 res2 op3 res3 -> SigMap op1 res1 op3 res3
Effect.sigCompose (MkSigMap i1 r1) (MkSigMap i2 r2) =
  MkSigMap (\o -> i2 (i1 o)) (\o r -> r1 o (r2 (i1 o) r))

-- Weakening: a signature into a row with something else on the right or left.
Effect.sigLeft : [l r : Type] -> [lres : l -> Type] -> [rres : r -> Type] ->
  SigMap l lres (Plus l r) (PlusRes lres rres)
Effect.sigLeft = MkSigMap (\o -> L o) (\o x -> x)

Effect.sigRight : [l r : Type] -> [lres : l -> Type] -> [rres : r -> Type] ->
  SigMap r rres (Plus l r) (PlusRes lres rres)
Effect.sigRight = MkSigMap (\o -> R o) (\o x -> x)

-- Reordering: `{l, r}` to `{r, l}`.
Effect.swapOp : [l r : Type] -> Plus l r -> Plus r l
Effect.swapOp (L o) = R o
Effect.swapOp (R o) = L o

Effect.swapReply : [l r : Type] -> [lres : l -> Type] -> [rres : r -> Type] ->
  (o : Plus l r) -> PlusRes rres lres (swapOp o) -> PlusRes lres rres o
Effect.swapReply (L o) x = x
Effect.swapReply (R o) x = x

Effect.sigSwap : [l r : Type] -> [lres : l -> Type] -> [rres : r -> Type] ->
  SigMap (Plus l r) (PlusRes lres rres) (Plus r l) (PlusRes rres lres)
Effect.sigSwap = MkSigMap swapOp swapReply

-- Support for abilities (docs/proposals/abilities.md). The elaborator
-- translates `ability`, rows `{A | e}`, effectful code and `handle` into these.

-- `()`: the unit type and its only value.
type Builtin.UnitType : Type =
  | UnitValue

-- The signature with no operations: the end of a closed row.
type Effect.NoOp : Type

Effect.NoRes : NoOp -> Type
Effect.NoRes ()

-- A signature as one value, so a row variable `e` is one parameter.
type Effect.Sig : Type 1 =
  | MkSig (op : Type) (res : op -> Type)

Effect.sigOp : Sig -> Type
Effect.sigOp (MkSig op res) = op

Effect.sigRes : (s : Sig) -> sigOp s -> Type
Effect.sigRes (MkSig op res) = res

-- Combining two mappings into one from `{l, r}`.
Effect.caseInject : [l r t : Type] -> [lres : l -> Type] -> [rres : r -> Type] -> [tres : t -> Type] ->
  SigMap l lres t tres -> SigMap r rres t tres -> Plus l r -> t
Effect.caseInject ml mr (L o) = sigInject ml o
Effect.caseInject ml mr (R o) = sigInject mr o

Effect.caseReply : [l r t : Type] -> [lres : l -> Type] -> [rres : r -> Type] -> [tres : t -> Type] ->
  (ml : SigMap l lres t tres) -> (mr : SigMap r rres t tres) ->
  (o : Plus l r) -> tres (caseInject ml mr o) -> PlusRes lres rres o
Effect.caseReply ml mr (L o) x = sigReply ml o x
Effect.caseReply ml mr (R o) x = sigReply mr o x

Effect.sigCase : [l r t : Type] -> [lres : l -> Type] -> [rres : r -> Type] -> [tres : t -> Type] ->
  SigMap l lres t tres -> SigMap r rres t tres -> SigMap (Plus l r) (PlusRes lres rres) t tres
Effect.sigCase ml mr = MkSigMap (caseInject ml mr) (caseReply ml mr)

-- The empty signature maps into anything.
Effect.noInject : [t : Type] -> NoOp -> t
Effect.noInject ()

Effect.noReply : [t : Type] -> [tres : t -> Type] -> (o : NoOp) -> tres (noInject o) -> NoRes o
Effect.noReply ()

Effect.sigFromNo : [t : Type] -> [tres : t -> Type] -> SigMap NoOp NoRes t tres
Effect.sigFromNo = MkSigMap noInject noReply

-- A handler's step for the row `{l, r}`, from steps for each side.
Effect.handlePlus : [l r : Type] -> [lres : l -> Type] -> [rres : r -> Type] -> [res : Type] ->
  ((o : l) -> (lres o -> res) -> res) -> ((o : r) -> (rres o -> res) -> res) ->
  (o : Plus l r) -> (PlusRes lres rres o -> res) -> res
Effect.handlePlus fl fr (L o) k = fl o k
Effect.handlePlus fl fr (R o) k = fr o k

-- A computation that performs nothing is just its result.
Effect.runPure : [a : Type] -> Comp NoOp NoRes a -> a
Effect.runPure (Done x)       = x
Effect.runPure (Call () rest)

-- Partial computations (docs/proposals/partial.md)

-- A recursion request: run the definition being defined again on `x`. A
-- partial definition's body makes these instead of calling itself.
type Effect.Rec (req : Type) : Type =
  | Recur (x : req)

-- What a request is answered with.
Effect.RecRes : [req : Type] -> (req -> Type) -> Rec req -> Type
Effect.RecRes ans (Recur x) = ans x

-- A computation that may not finish: what `{Partial | e} a` stands for.
-- These have no definitions, and nothing can look inside a `Delay`: only
-- the runtime runs one, a step at a time. The kernel admits them as
-- primitives, after checking their types are exactly these.
Effect.Delay : (op : Type) -> (res : op -> Type) -> Type -> Type

-- Finished, with this result.
Effect.now : [op : Type] -> [res : op -> Type] -> [a : Type] -> a -> Delay op res a

-- A computation that finishes, as one that might not.
Effect.lift : [op : Type] -> [res : op -> Type] -> [a : Type] -> Comp op res a -> Delay op res a

-- Sequencing.
Effect.bindD : [op : Type] -> [res : op -> Type] -> [a b : Type] ->
  Delay op res a -> (a -> Delay op res b) -> Delay op res b

-- Moves a computation along a mapping between signatures.
Effect.mapSig : [op1 : Type] -> [res1 : op1 -> Type] -> [op2 : Type] -> [res2 : op2 -> Type] -> [a : Type] ->
  SigMap op1 res1 op2 res2 -> Delay op1 res1 a -> Delay op2 res2 a

-- The recursive function a description defines: each `Recur y` its body
-- requests is answered by running the body on `y`.
Effect.pfix : [op : Type] -> [res : op -> Type] -> [req : Type] -> [ans : req -> Type] ->
  ((x : req) -> Delay (Plus (Rec req) op) (PlusRes (RecRes ans) res) (ans x)) ->
  (x : req) -> Delay op res (ans x)

-- Decimal digits, most significant first: `Nat.digits 1205` is `[1, 2, 0, 5]`
-- and `Nat.digits 0` is `[0]`. The fuel is `n + 1`, more than the digits need.
Nat.digitsFuel : Nat -> Nat -> List Nat -> List Nat
Nat.digitsFuel Zero        n acc = Cons n acc
Nat.digitsFuel (Succ fuel) n acc =
  if Nat.leq n 9 then Cons n acc else Nat.digitsFuel fuel (n / 10) (Cons (n % 10) acc)

Nat.digits : Nat -> List Nat
Nat.digits n = Nat.digitsFuel (Succ n) n Nil

-- The number whose decimal digits these are, most significant first. Digits
-- above 9 carry into their neighbours: it is `Nat.digits`'s inverse only on
-- real digit lists.
Nat.fromDigits : List Nat -> Nat
Nat.fromDigits ds = List.foldl (\acc d -> acc * 10 + d) 0 ds


theorem Nat.digitsZero : Nat.digits 0 = [0]
Nat.digitsZero = rfl

theorem Nat.digitsExample : Nat.digits 1205 = [1, 2, 0, 5]
Nat.digitsExample = rfl

theorem Nat.fromDigitsExample : Nat.fromDigits [1, 2, 0, 5] = 1205
Nat.fromDigitsExample = rfl

theorem Nat.digitsSeven : Nat.digits 7 = [7]
Nat.digitsSeven = rfl

theorem Nat.digitsTen : Nat.digits 10 = [1, 0]
Nat.digitsTen = rfl

theorem Nat.fromDigitsNil : Nat.fromDigits Nil = 0
Nat.fromDigitsNil = rfl

theorem Nat.digitsRoundTrip : Nat.fromDigits (Nat.digits 9876543210) = 9876543210
Nat.digitsRoundTrip = rfl

-- Input and output (docs/proposals/text-and-io.md, Part 2)

-- The console. Only a host interpreter performs these for real; in Stitchwort
-- code, `IO.simulate` interprets them as data.
ability IO where
  print    : Text -> {IO} ()          -- writes the text, then a line ending
  readLine : () -> {IO} (Maybe Text)  -- Nothing only at end of input

-- The first line of scripted input, if there is one.
IO.nextLine : List Text -> Maybe Text
IO.nextLine Nil         = Nothing
IO.nextLine (Cons l ls) = Just l

-- Runs a program against scripted input lines: each `readLine` takes the
-- next one, and gives `Nothing` once they're used up. Records each `print`
-- payload, in order, with the result. A payload is one entry even if it
-- contains a line feed: a real interpreter writes each payload followed by
-- a line ending. The payloads are collected in reverse and turned round at
-- the end, so a long run doesn't build a deep chain of pending pairs.
IO.simulate : List Text -> (() -> {IO | e} a) -> {e} Pair (List Text) a
IO.simulate input prog =
  let run : List Text -> List Text -> {e} Pair (List Text) a =
    handle prog () with
      | return x        -> \ins out -> MkPair (List.reverseOnto out Nil) x
      | print t => k    -> \ins out -> k () ins (Cons t out)
      | readLine u => k -> \ins out -> k (IO.nextLine ins) (List.tailOf ins) out
  run input Nil

-- Reading all of the input

-- What to do with the next line, given the lines so far (newest first): keep
-- going, or stop at the end of the input. `more` is whatever comes next, so
-- this isn't recursive, and is polymorphic in the rest of the row (see
-- examples/accept/cat.sw).
IO.readLinesStep : List Text -> Maybe Text -> (List Text -> {IO, Partial | e} (List Text)) -> {IO, Partial | e} (List Text)
IO.readLinesStep acc Nothing  more = List.reverse acc
IO.readLinesStep acc (Just l) more = more (Cons l acc)

IO.readLinesFrom : List Text -> {IO, Partial} (List Text)
IO.readLinesFrom acc = IO.readLinesStep acc (readLine ()) IO.readLinesFrom

-- Every remaining line of input, in order, up to the end of the input. There
-- is no bound on how many, so it is `Partial`: only `stitchwort run` and the
-- playground can run it.
IO.readAllLines : () -> {IO, Partial} (List Text)
IO.readAllLines u = IO.readLinesFrom Nil
