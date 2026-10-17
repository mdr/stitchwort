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
Nat.digits : Nat -> Nat -> List Char -> List Char
Nat.digits Zero        n acc = acc
Nat.digits (Succ fuel) n acc =
  if Nat.leq n 9 then Cons (Nat.digitChar n) acc else Nat.digits fuel (n / 10) (Cons (Nat.digitChar (n % 10)) acc)

-- Decimal, without leading zeros: `Nat.toText 42` is `"42"`.
Nat.toText : Nat -> Text
Nat.toText n = MkText (Nat.digits (Succ n) n Nil)

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
