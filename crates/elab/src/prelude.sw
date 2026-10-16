-- The Stitchwort prelude, loaded before every file.

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
absurd : Void -> a
absurd ()

-- The same for proofs. (Without universe polymorphism, `absurd`'s `a` can
-- only be a type of data.)
exfalso : [p : Prop] -> Void -> p
exfalso ()

-- Numbers

-- Numbers are stored compactly, but mean exactly this. `add`, `sub`, `mul`,
-- `leq`, `eqNat`, `divFuel`, `decEqNat`, `eqNatRefl` and `eqNatSound` also
-- have native implementations, used when all their arguments are numbers.
-- Each computes exactly what the definition here computes, proofs included;
-- they're tested against these definitions.
type Nat : Type =
  | Zero
  | Succ (n : Nat)

-- `a + b` means `add a b`. It recurses on its first argument, so
-- `Succ m + n` computes to `Succ (m + n)`.
add : Nat -> Nat -> Nat
add Zero     n = n
add (Succ m) n = Succ (add m n)

-- `a - b`, stopping at zero: `3 - 5 = 0`.
sub : Nat -> Nat -> Nat
sub m        Zero     = m
sub Zero     (Succ n) = Zero
sub (Succ m) (Succ n) = sub m n

-- `a * b`
mul : Nat -> Nat -> Nat
mul Zero     n = 0
mul (Succ m) n = n + mul m n

pred : Nat -> Nat
pred Zero     = Zero
pred (Succ n) = n

-- Booleans

type Bool : Type =
  | False
  | True

not : Bool -> Bool
not False = True
not True  = False

-- `if c then a else b`. The branches take a (unused) proof of `Unit` so that
-- only the chosen one is evaluated.
ifThenElse : [a : Type] -> Bool -> (Unit -> a) -> (Unit -> a) -> a
ifThenElse True  t e = t Trivial
ifThenElse False t e = e Trivial

-- `m <= n` and `m < n` are propositions, defined by computation.
leq : Nat -> Nat -> Bool
leq Zero     n        = True
leq (Succ m) Zero     = False
leq (Succ m) (Succ n) = leq m n

LessEq : Nat -> Nat -> Prop
LessEq m n = leq m n = True

LessThan : Nat -> Nat -> Prop
LessThan m n = leq (Succ m) n = True

-- Lists

type List (a : Type) : Type =
  | Nil
  | Cons (head : a) (tail : List a)

-- `a` is bound automatically, as an implicit argument: `length : [a : Type] -> ...`.
length : List a -> Nat
length Nil         = 0
length (Cons x xs) = Succ (length xs)

append : List a -> List a -> List a
append Nil         ys = ys
append (Cons x xs) ys = Cons x (append xs ys)

-- A value that may be missing.
type Maybe (a : Type) : Type =
  | Nothing
  | Just (value : a)

-- Two values together.
type Pair (a : Type) (b : Type) : Type =
  | MkPair (fst : a) (snd : b)

fst : Pair a b -> a
fst (MkPair x y) = x

snd : Pair a b -> b
snd (MkPair x y) = y

-- `reverseOnto xs acc` is `xs` reversed, followed by `acc`.
reverseOnto : List a -> List a -> List a
reverseOnto Nil         acc = acc
reverseOnto (Cons x xs) acc = reverseOnto xs (Cons x acc)

-- Equality lemmas, all built from `J`.

theorem cong : (f : a -> b) -> [x y : a] -> x = y -> f x = f y
cong f p = J (\y' p' -> f x = f y') rfl p

theorem sym : [x y : a] -> x = y -> y = x
sym p = J (\y' p' -> y' = x) rfl p

theorem trans : [x y z : a] -> x = y -> y = z -> x = z
trans p q = J (\z' q' -> x = z') p q

-- Different constructors are different. Each proof transports along the
-- equation into a family that's `Unit` at one constructor and `Void` at the other.

IsZero : Nat -> Prop
IsZero Zero     = Unit
IsZero (Succ n) = Void

theorem zeroNotSucc : (n : Nat) -> Not (0 = Succ n)
zeroNotSucc n p = J (\y q -> IsZero y) Trivial p

theorem succNotZero : (n : Nat) -> Not (Succ n = 0)
succNotZero n p = zeroNotSucc n (sym p)

theorem succInjective : (m : Nat) -> (n : Nat) -> Succ m = Succ n -> m = n
succInjective m n p = cong pred p

IsFalse : Bool -> Prop
IsFalse False = Unit
IsFalse True  = Void

theorem falseNotTrue : Not (False = True)
falseNotTrue p = J (\y q -> IsFalse y) Trivial p

-- Whether two numbers are equal, as a `Bool`.
eqNat : Nat -> Nat -> Bool
eqNat Zero     Zero     = True
eqNat Zero     (Succ n) = False
eqNat (Succ m) Zero     = False
eqNat (Succ m) (Succ n) = eqNat m n

theorem eqNatRefl : (n : Nat) -> eqNat n n = True
eqNatRefl Zero     = rfl
eqNatRefl (Succ n) = eqNatRefl n

-- Numbers that `eqNat` says are equal are equal.
theorem eqNatSound : (m : Nat) -> (n : Nat) -> eqNat m n = True -> m = n
eqNatSound Zero     Zero     h = rfl
eqNatSound Zero     (Succ n) h = exfalso (falseNotTrue h)
eqNatSound (Succ m) Zero     h = exfalso (falseNotTrue h)
eqNatSound (Succ m) (Succ n) h = cong Succ (eqNatSound m n h)

-- Numbers that `eqNat` says differ are different.
theorem natNeq : (m : Nat) -> (n : Nat) -> eqNat m n = False -> Not (m = n)
natNeq m n h p = falseNotTrue (trans (sym h) (J (\y q -> eqNat m y = True) (eqNatRefl m) p))

-- Decisions

-- Either a proof of `p` or a proof that `p` is false. Whether it's `Yes` or
-- `No` exists at runtime; the proofs inside are erased.
type Decidable (p : Prop) : Type =
  | Yes (proof : p)
  | No (refutation : Not p)

-- `IsYes d` is `Unit` (provable) exactly when `d` is `Yes`.
IsYes : Decidable p -> Prop
IsYes (Yes h) = Unit
IsYes (No r)  = Void

-- How `auto` turns a decision into a proof: `fromYes d Trivial` only checks
-- when `d` computes to `Yes`.
fromYes : [p : Prop] -> (d : Decidable p) -> IsYes d -> p
fromYes (Yes h) u = h
fromYes (No r)  u = exfalso u

-- `a == b` is `toBool d`, for a decision procedure `d` for `a = b`.
toBool : [p : Prop] -> Decidable p -> Bool
toBool (Yes h) = True
toBool (No r)  = False

-- `if h : p then a else b`
elimDec : [p : Prop] -> [a : Type] -> Decidable p -> (p -> a) -> (Not p -> a) -> a
elimDec (Yes h) yes no = yes h
elimDec (No r)  yes no = no r

-- Decision procedures. `auto` and `if h : …` use any function returning
-- `Decidable …`.

decTrue : (b : Bool) -> Decidable (b = True)
decTrue True  = Yes rfl
decTrue False = No falseNotTrue

decSucc : (m : Nat) -> (n : Nat) -> Decidable (m = n) -> Decidable (Succ m = Succ n)
decSucc m n (Yes p) = Yes (cong Succ p)
decSucc m n (No r)  = No (\p -> r (succInjective m n p))

-- A decision from what `eqNat` says.
decEqNatFrom : (m : Nat) -> (n : Nat) -> (b : Bool) -> eqNat m n = b -> Decidable (m = n)
decEqNatFrom m n True  h = Yes (eqNatSound m n h)
decEqNatFrom m n False h = No (natNeq m n h)

-- For two numbers this computes `Yes rfl` or `No (natNeq m n rfl)`, and the
-- native gives exactly that, however big they are. (Recursing with `decSucc`
-- would build a refutation as deep as the smaller number.) It matches on
-- both numbers so it waits until they're known, rather than unfolding around
-- an unknown one.
decEqNat : (m : Nat) -> (n : Nat) -> Decidable (m = n)
decEqNat Zero     Zero     = Yes rfl
decEqNat Zero     (Succ n) = No (natNeq 0 (Succ n) rfl)
decEqNat (Succ m) Zero     = No (natNeq (Succ m) 0 rfl)
decEqNat (Succ m) (Succ n) = decEqNatFrom (Succ m) (Succ n) (eqNat m n) rfl

theorem trueNotFalse : Not (True = False)
trueNotFalse p = falseNotTrue (sym p)

decEqBool : (a : Bool) -> (b : Bool) -> Decidable (a = b)
decEqBool False False = Yes rfl
decEqBool False True  = No falseNotTrue
decEqBool True  False = No trueNotFalse
decEqBool True  True  = Yes rfl

decNot : [p : Prop] -> Decidable p -> Decidable (Not p)
decNot (Yes h) = No (\n -> n h)
decNot (No r)  = Yes r

decLessEq : (m : Nat) -> (n : Nat) -> Decidable (m <= n)
decLessEq m n = decTrue (leq m n)

decLessThan : (m : Nat) -> (n : Nat) -> Decidable (m < n)
decLessThan m n = decTrue (leq (Succ m) n)

-- Proofs that two booleans are equal are unique. This is Hedberg's argument,
-- which works for any type with decidable equality: `canon` turns any proof
-- of `x = y` into one chosen by `decEqBool`, so it ignores which proof it was
-- given, and every proof can be recovered from its canonical one.
canon : [x y : Bool] -> Decidable (x = y) -> x = y -> x = y
canon (Yes e) p = e
canon (No r)  p = exfalso (r p)

theorem canonConst : [x y : Bool] -> (d : Decidable (x = y)) -> (p : x = y) -> (q : x = y) ->
  canon d p = canon d q
canonConst (Yes e) p q = rfl
canonConst (No r)  p q = exfalso (r p)

theorem symThenSelf : [x y : Bool] -> (q : x = y) -> rfl = trans (sym q) q
symThenSelf q = J (\y' q' -> rfl = trans (sym q') q') rfl q

theorem fromCanon : (x : Bool) -> (y : Bool) -> (p : x = y) ->
  p = trans (sym (canon (decEqBool x x) rfl)) (canon (decEqBool x y) p)
fromCanon x y p =
  J (\y' p' -> p' = trans (sym (canon (decEqBool x x) rfl)) (canon (decEqBool x y') p'))
    (symThenSelf (canon (decEqBool x x) rfl)) p

theorem uniqueBoolEq : (x : Bool) -> (y : Bool) -> (p : x = y) -> (q : x = y) -> p = q
uniqueBoolEq x y p q =
  J (\z e -> p = z)
    (J (\r e -> p = trans (sym (canon (decEqBool x x) rfl)) r)
      (fromCanon x y p) (canonConst (decEqBool x y) p q))
    (J (\z e -> z = q) rfl (fromCanon x y q))

-- Characters

-- Whether a number is a Unicode scalar value: at most 0x10FFFF, and not a
-- surrogate (0xD800 to 0xDFFF).
isScalar : Nat -> Bool
isScalar n = if leq 55296 n then (if leq n 57343 then False else leq n 1114111) else True

-- A Unicode scalar value. `'a'` is a `Char`; the compiler proves `valid` for
-- a literal by computation, and the kernel checks it.
type Char : Type =
  | MkChar (code : Nat) (valid : isScalar code = True)

charToNat : Char -> Nat
charToNat (MkChar n v) = n

charFromNat : Nat -> Maybe Char
charFromNat n = if h : isScalar n = True then Just (MkChar n h) else Nothing

-- Characters with the same code are equal: their proofs of `valid` are too.
theorem mkCharExt : (a : Nat) -> (b : Nat) -> (p : isScalar a = True) -> a = b ->
  (q : isScalar b = True) -> MkChar a p = MkChar b q
mkCharExt a b p e =
  J (\b' e' -> (q' : isScalar b' = True) -> MkChar a p = MkChar b' q')
    (\q' -> J (\r e'' -> MkChar a p = MkChar a r) rfl (uniqueBoolEq (isScalar a) True p q'))
    e

theorem charExt : (x : Char) -> (y : Char) -> charToNat x = charToNat y -> x = y
charExt (MkChar a p) (MkChar b q) e = mkCharExt a b p e q

decCharFrom : (x : Char) -> (y : Char) -> Decidable (charToNat x = charToNat y) -> Decidable (x = y)
decCharFrom x y (Yes e) = Yes (charExt x y e)
decCharFrom x y (No r)  = No (\p -> r (cong charToNat p))

decEqChar : (x : Char) -> (y : Char) -> Decidable (x = y)
decEqChar x y = decCharFrom x y (decEqNat (charToNat x) (charToNat y))

-- Division

-- Counts how many times `d` fits into `n`, using `fuel` to stay structurally
-- recursive (`n` is always enough fuel when `d` isn't zero).
divFuel : Nat -> Nat -> Nat -> Nat
divFuel Zero        n d = 0
divFuel (Succ fuel) n d = if leq d n then Succ (divFuel fuel (n - d) d) else 0

-- `n / d` and `n % d` need a proof that `d` isn't zero, which `auto` finds.
div : (n : Nat) -> (d : Nat) -> [auto ok : d != 0] -> Nat
div n d = divFuel n n d

mod : (n : Nat) -> (d : Nat) -> [auto ok : d != 0] -> Nat
mod n d = n - d * (n / d)

-- Lists, continued

theorem lengthAppend : (xs : List a) -> (ys : List a) -> length (append xs ys) = length xs + length ys
lengthAppend Nil         ys = rfl
lengthAppend (Cons x xs) ys = cong Succ (lengthAppend xs ys)

IsNil : List a -> Prop
IsNil Nil         = Unit
IsNil (Cons x xs) = Void

theorem nilNotCons : (x : a) -> (xs : List a) -> Not (Nil = Cons x xs)
nilNotCons x xs p = J (\y q -> IsNil y) Trivial p

theorem consNotNil : (x : a) -> (xs : List a) -> Not (Cons x xs = Nil)
consNotNil x xs p = nilNotCons x xs (sym p)

headOr : a -> List a -> a
headOr d Nil         = d
headOr d (Cons x xs) = x

tailOf : List a -> List a
tailOf Nil         = Nil
tailOf (Cons x xs) = xs

decCons : (x : a) -> (y : a) -> (xs : List a) -> (ys : List a) ->
  Decidable (x = y) -> Decidable (xs = ys) -> Decidable (Cons x xs = Cons y ys)
decCons x y xs ys (Yes p) (Yes q) = Yes (J (\y' p' -> Cons x xs = Cons y' ys) (cong (Cons x) q) p)
decCons x y xs ys (No r)  dq      = No (\e -> r (cong (headOr x) e))
decCons x y xs ys (Yes p) (No r)  = No (\e -> r (cong tailOf e))

-- Equality of lists, from equality of their elements.
decEqList : ((x : a) -> (y : a) -> Decidable (x = y)) -> (xs : List a) -> (ys : List a) -> Decidable (xs = ys)
decEqList d Nil         Nil         = Yes rfl
decEqList d Nil         (Cons y ys) = No (nilNotCons y ys)
decEqList d (Cons x xs) Nil         = No (consNotNil x xs)
decEqList d (Cons x xs) (Cons y ys) = decCons x y xs ys (d x y) (decEqList d xs ys)

-- Comparisons

type Ordering : Type =
  | Less
  | Equal
  | Greater

compareNat : Nat -> Nat -> Ordering
compareNat m n = if eqNat m n then Equal else (if leq m n then Less else Greater)

-- The first comparison, unless it's `Equal`.
thenCompare : Ordering -> Ordering -> Ordering
thenCompare Less    o = Less
thenCompare Equal   o = o
thenCompare Greater o = Greater

isLess : Ordering -> Bool
isLess Less    = True
isLess Equal   = False
isLess Greater = False

-- Text (docs/proposals/text-and-io.md)

-- A sequence of Unicode scalar values. `"héllo"` is a `Text`. Equality and
-- ordering compare the sequence exactly, by scalar value, and length counts
-- scalar values; nothing is normalised, so `"\u{E9}"` and `"e\u{301}"` are
-- different texts. Code that goes through `textToList` and `textFromList`
-- and their lemmas, rather than `MkText`, won't depend on the representation.
type Text : Type =
  | MkText (chars : List Char)

textToList : Text -> List Char
textToList (MkText cs) = cs

textFromList : List Char -> Text
textFromList cs = MkText cs

theorem textToFromList : (cs : List Char) -> textToList (textFromList cs) = cs
textToFromList cs = rfl

theorem textFromToList : (t : Text) -> textFromList (textToList t) = t
textFromToList (MkText cs) = rfl

-- `a ++ b`
textAppend : Text -> Text -> Text
textAppend a b = MkText (append (textToList a) (textToList b))

-- The number of scalar values.
textLength : Text -> Nat
textLength t = length (textToList t)

theorem textLengthAppend : (a : Text) -> (b : Text) ->
  textLength (textAppend a b) = textLength a + textLength b
textLengthAppend a b = lengthAppend (textToList a) (textToList b)

textIsEmpty : Text -> Bool
textIsEmpty (MkText Nil)         = True
textIsEmpty (MkText (Cons c cs)) = False

decTextFrom : (a : Text) -> (b : Text) -> Decidable (textToList a = textToList b) -> Decidable (a = b)
decTextFrom a b (Yes p) = Yes (trans (sym (textFromToList a)) (trans (cong textFromList p) (textFromToList b)))
decTextFrom a b (No r)  = No (\p -> r (cong textToList p))

decEqText : (a : Text) -> (b : Text) -> Decidable (a = b)
decEqText a b = decTextFrom a b (decEqList decEqChar (textToList a) (textToList b))

-- The first character and the rest, unless the text is empty.
textUncons : Text -> Maybe (Pair Char Text)
textUncons (MkText Nil)         = Nothing
textUncons (MkText (Cons c cs)) = Just (MkPair c (MkText cs))

foldChars : (Char -> b -> b) -> b -> List Char -> b
foldChars f z Nil         = z
foldChars f z (Cons c cs) = f c (foldChars f z cs)

-- `textFold f z "abc"` is `f 'a' (f 'b' (f 'c' z))`.
textFold : (Char -> b -> b) -> b -> Text -> b
textFold f z t = foldChars f z (textToList t)

compareChars : List Char -> List Char -> Ordering
compareChars Nil         Nil         = Equal
compareChars Nil         (Cons y ys) = Less
compareChars (Cons x xs) Nil         = Greater
compareChars (Cons x xs) (Cons y ys) =
  thenCompare (compareNat (charToNat x) (charToNat y)) (compareChars xs ys)

-- Lexicographic, by scalar value. (Not JavaScript's order, which compares
-- UTF-16 code units: there, "\u{10000}" sorts before "\u{E000}".)
textCompare : Text -> Text -> Ordering
textCompare a b = compareChars (textToList a) (textToList b)

textLess : Text -> Text -> Bool
textLess a b = isLess (textCompare a b)

-- Whitespace, for `textTrim`: exactly space, tab, line feed, vertical tab,
-- form feed and carriage return. Not Unicode's `White_Space`.
isSpaceCode : Nat -> Bool
isSpaceCode 9  = True
isSpaceCode 10 = True
isSpaceCode 11 = True
isSpaceCode 12 = True
isSpaceCode 13 = True
isSpaceCode 32 = True
isSpaceCode _  = False

isSpace : Char -> Bool
isSpace c = isSpaceCode (charToNat c)

dropSpaces : List Char -> List Char
dropSpaces Nil         = Nil
dropSpaces (Cons c cs) = if isSpace c then dropSpaces cs else Cons c cs

-- Removes whitespace (as `isSpace` defines it) from both ends.
textTrim : Text -> Text
textTrim t = MkText (reverseOnto (dropSpaces (reverseOnto (dropSpaces (textToList t)) Nil)) Nil)

-- Numbers as text

digitChar : Nat -> Char
digitChar 0 = '0'
digitChar 1 = '1'
digitChar 2 = '2'
digitChar 3 = '3'
digitChar 4 = '4'
digitChar 5 = '5'
digitChar 6 = '6'
digitChar 7 = '7'
digitChar 8 = '8'
digitChar _ = '9'

-- The digits of `n` in front of `acc`. `fuel` keeps it structurally
-- recursive; `n + 1` is always enough.
natDigits : Nat -> Nat -> List Char -> List Char
natDigits Zero        n acc = acc
natDigits (Succ fuel) n acc =
  if leq n 9 then Cons (digitChar n) acc else natDigits fuel (n / 10) (Cons (digitChar (n % 10)) acc)

-- Decimal, without leading zeros: `natToText 42` is `"42"`.
natToText : Nat -> Text
natToText n = MkText (natDigits (Succ n) n Nil)

maybeThen : Maybe a -> (a -> Maybe b) -> Maybe b
maybeThen Nothing  f = Nothing
maybeThen (Just x) f = f x

digitValue : Char -> Maybe Nat
digitValue c = if leq 48 (charToNat c) then (if leq (charToNat c) 57 then Just (charToNat c - 48) else Nothing) else Nothing

readDigits : Nat -> List Char -> Maybe Nat
readDigits acc Nil         = Just acc
readDigits acc (Cons c cs) = maybeThen (digitValue c) (\d -> readDigits (acc * 10 + d) cs)

-- A non-empty sequence of ASCII digits, and nothing else: no sign,
-- whitespace or separators. Leading zeros are allowed, so
-- `textToNat (natToText n) = Just n` but `"007"` reads as 7.
textToNat : Text -> Maybe Nat
textToNat (MkText Nil)         = Nothing
textToNat (MkText (Cons c cs)) = readDigits 0 (Cons c cs)

-- Splitting and joining

-- `splitChars s cs` is the first field and the rest: never empty.
splitCons : Char -> Char -> Bool -> Pair (List Char) (List (List Char)) -> Pair (List Char) (List (List Char))
splitCons s c True  (MkPair f fs) = MkPair Nil (Cons f fs)
splitCons s c False (MkPair f fs) = MkPair (Cons c f) fs

splitChars : Char -> List Char -> Pair (List Char) (List (List Char))
splitChars s Nil         = MkPair Nil Nil
splitChars s (Cons c cs) = splitCons s c (toBool (decEqChar c s)) (splitChars s cs)

joinChars : Char -> List Char -> List (List Char) -> List Char
joinChars s f Nil         = f
joinChars s f (Cons g gs) = append f (Cons s (joinChars s g gs))

joinPair : Char -> Pair (List Char) (List (List Char)) -> List Char
joinPair s (MkPair f fs) = joinChars s f fs

theorem joinCons : (s : Char) -> (c : Char) -> (f : List Char) -> (fs : List (List Char)) ->
  joinChars s (Cons c f) fs = Cons c (joinChars s f fs)
joinCons s c f Nil         = rfl
joinCons s c f (Cons g gs) = rfl

theorem joinSplitCons : (s : Char) -> (c : Char) -> (cs : List Char) ->
  (p : Pair (List Char) (List (List Char))) -> joinPair s p = cs ->
  (d : Decidable (c = s)) -> joinPair s (splitCons s c (toBool d) p) = Cons c cs
joinSplitCons s c cs (MkPair f fs) h (Yes e) =
  trans (cong (Cons s) h) (cong (\x -> Cons x cs) (sym e))
joinSplitCons s c cs (MkPair f fs) h (No r) =
  trans (joinCons s c f fs) (cong (Cons c) h)

theorem joinSplitChars : (s : Char) -> (cs : List Char) -> joinPair s (splitChars s cs) = cs
joinSplitChars s Nil         = rfl
joinSplitChars s (Cons c cs) =
  joinSplitCons s c cs (splitChars s cs) (joinSplitChars s cs) (decEqChar c s)

textsOf : List (List Char) -> List Text
textsOf Nil         = Nil
textsOf (Cons f fs) = Cons (MkText f) (textsOf fs)

charListsOf : List Text -> List (List Char)
charListsOf Nil         = Nil
charListsOf (Cons t ts) = Cons (textToList t) (charListsOf ts)

theorem charListsOfTexts : (fs : List (List Char)) -> charListsOf (textsOf fs) = fs
charListsOfTexts Nil         = rfl
charListsOfTexts (Cons f fs) = cong (Cons f) (charListsOfTexts fs)

splitTexts : Pair (List Char) (List (List Char)) -> List Text
splitTexts (MkPair f fs) = Cons (MkText f) (textsOf fs)

-- The fields between separators, keeping empty ones: splitting "a,,b" on
-- ',' gives ["a", "", "b"], and splitting "" gives [""].
textSplit : Char -> Text -> List Text
textSplit s t = splitTexts (splitChars s (textToList t))

-- The texts with `s` between them. `textJoin s (textSplit s t) = t`.
textJoin : Char -> List Text -> Text
textJoin s Nil         = MkText Nil
textJoin s (Cons t ts) = MkText (joinChars s (textToList t) (charListsOf ts))

theorem joinSplitTexts : (s : Char) -> (p : Pair (List Char) (List (List Char))) ->
  textJoin s (splitTexts p) = MkText (joinPair s p)
joinSplitTexts s (MkPair f fs) = cong (\l -> MkText (joinChars s f l)) (charListsOfTexts fs)

theorem textJoinSplit : (s : Char) -> (t : Text) -> textJoin s (textSplit s t) = t
textJoinSplit s (MkText cs) =
  trans (joinSplitTexts s (splitChars s cs)) (cong MkText (joinSplitChars s cs))

-- Computations (docs/proposals/abilities.md)

-- A computation that returns an `a`, performing operations from a signature:
-- `op` is the type of operation calls, and `res o` is what call `o` gives
-- back. Every computation is a finite tree, so folds over it terminate.
type Comp (op : Type) (res : op -> Type) (a : Type) : Type =
  | Done (value : a)
  | Call (o : op) (rest : res o -> Comp op res a)

-- The fold over a computation. `call` gets each operation together with the
-- results of folding every way it could continue, and may use them any
-- number of times. A deep handler is a fold.
foldComp : [op : Type] -> [res : op -> Type] -> [a r : Type] ->
  (a -> r) -> ((o : op) -> (res o -> r) -> r) -> Comp op res a -> r
foldComp done call (Done x)      = done x
foldComp done call (Call o rest) = call o (\y -> foldComp done call (rest y))

-- Sequencing: run `c`, then `next` with its result.
bind : [op : Type] -> [res : op -> Type] -> [a b : Type] ->
  Comp op res a -> (a -> Comp op res b) -> Comp op res b
bind (Done x)      next = next x
bind (Call o rest) next = Call o (\y -> bind (rest y) next)

-- Rows: signatures side by side, and mappings between signatures.

-- The operations of two signatures: the row `{l, r}`.
type Plus (l : Type) (r : Type) : Type =
  | L (o : l)
  | R (o : r)

PlusRes : [l r : Type] -> (l -> Type) -> (r -> Type) -> Plus l r -> Type
PlusRes lres rres (L o) = lres o
PlusRes lres rres (R o) = rres o

-- A mapping from one signature into another. Because what an operation
-- returns depends on the operation, a mapping says both where each
-- operation goes and how its response comes back.
type SigMap (op1 : Type) (res1 : op1 -> Type) (op2 : Type) (res2 : op2 -> Type) : Type =
  | MkSigMap (inject : op1 -> op2) (reply : (o : op1) -> res2 (inject o) -> res1 o)

sigInject : [op1 : Type] -> [res1 : op1 -> Type] -> [op2 : Type] -> [res2 : op2 -> Type] ->
  SigMap op1 res1 op2 res2 -> op1 -> op2
sigInject (MkSigMap inj rep) o = inj o

sigReply : [op1 : Type] -> [res1 : op1 -> Type] -> [op2 : Type] -> [res2 : op2 -> Type] ->
  (m : SigMap op1 res1 op2 res2) -> (o : op1) -> res2 (sigInject m o) -> res1 o
sigReply (MkSigMap inj rep) o r = rep o r

-- Moves a computation along a mapping. Operations stay in the same order;
-- only their names in the signature change.
translate : [op1 : Type] -> [res1 : op1 -> Type] -> [op2 : Type] -> [res2 : op2 -> Type] -> [a : Type] ->
  SigMap op1 res1 op2 res2 -> Comp op1 res1 a -> Comp op2 res2 a
translate m (Done x)      = Done x
translate m (Call o rest) = Call (sigInject m o) (\r -> translate m (rest (sigReply m o r)))

sigId : [op : Type] -> [res : op -> Type] -> SigMap op res op res
sigId = MkSigMap (\o -> o) (\o r -> r)

sigCompose : [op1 : Type] -> [res1 : op1 -> Type] -> [op2 : Type] -> [res2 : op2 -> Type] ->
  [op3 : Type] -> [res3 : op3 -> Type] ->
  SigMap op1 res1 op2 res2 -> SigMap op2 res2 op3 res3 -> SigMap op1 res1 op3 res3
sigCompose (MkSigMap i1 r1) (MkSigMap i2 r2) =
  MkSigMap (\o -> i2 (i1 o)) (\o r -> r1 o (r2 (i1 o) r))

-- Weakening: a signature into a row with something else on the right or left.
sigLeft : [l r : Type] -> [lres : l -> Type] -> [rres : r -> Type] ->
  SigMap l lres (Plus l r) (PlusRes lres rres)
sigLeft = MkSigMap (\o -> L o) (\o x -> x)

sigRight : [l r : Type] -> [lres : l -> Type] -> [rres : r -> Type] ->
  SigMap r rres (Plus l r) (PlusRes lres rres)
sigRight = MkSigMap (\o -> R o) (\o x -> x)

-- Reordering: `{l, r}` to `{r, l}`.
swapOp : [l r : Type] -> Plus l r -> Plus r l
swapOp (L o) = R o
swapOp (R o) = L o

swapReply : [l r : Type] -> [lres : l -> Type] -> [rres : r -> Type] ->
  (o : Plus l r) -> PlusRes rres lres (swapOp o) -> PlusRes lres rres o
swapReply (L o) x = x
swapReply (R o) x = x

sigSwap : [l r : Type] -> [lres : l -> Type] -> [rres : r -> Type] ->
  SigMap (Plus l r) (PlusRes lres rres) (Plus r l) (PlusRes rres lres)
sigSwap = MkSigMap swapOp swapReply

-- Support for abilities (docs/proposals/abilities.md). The elaborator
-- translates `ability`, rows `{A | e}`, effectful code and `handle` into these.

-- `()`: the unit type and its only value.
type UnitType : Type =
  | UnitValue

-- The signature with no operations: the end of a closed row.
type NoOp : Type

NoRes : NoOp -> Type
NoRes ()

-- A signature as one value, so a row variable `e` is one parameter.
type Sig : Type 1 =
  | MkSig (op : Type) (res : op -> Type)

sigOp : Sig -> Type
sigOp (MkSig op res) = op

sigRes : (s : Sig) -> sigOp s -> Type
sigRes (MkSig op res) = res

-- Combining two mappings into one from `{l, r}`.
caseInject : [l r t : Type] -> [lres : l -> Type] -> [rres : r -> Type] -> [tres : t -> Type] ->
  SigMap l lres t tres -> SigMap r rres t tres -> Plus l r -> t
caseInject ml mr (L o) = sigInject ml o
caseInject ml mr (R o) = sigInject mr o

caseReply : [l r t : Type] -> [lres : l -> Type] -> [rres : r -> Type] -> [tres : t -> Type] ->
  (ml : SigMap l lres t tres) -> (mr : SigMap r rres t tres) ->
  (o : Plus l r) -> tres (caseInject ml mr o) -> PlusRes lres rres o
caseReply ml mr (L o) x = sigReply ml o x
caseReply ml mr (R o) x = sigReply mr o x

sigCase : [l r t : Type] -> [lres : l -> Type] -> [rres : r -> Type] -> [tres : t -> Type] ->
  SigMap l lres t tres -> SigMap r rres t tres -> SigMap (Plus l r) (PlusRes lres rres) t tres
sigCase ml mr = MkSigMap (caseInject ml mr) (caseReply ml mr)

-- The empty signature maps into anything.
noInject : [t : Type] -> NoOp -> t
noInject ()

noReply : [t : Type] -> [tres : t -> Type] -> (o : NoOp) -> tres (noInject o) -> NoRes o
noReply ()

sigFromNo : [t : Type] -> [tres : t -> Type] -> SigMap NoOp NoRes t tres
sigFromNo = MkSigMap noInject noReply

-- A handler's step for the row `{l, r}`, from steps for each side.
handlePlus : [l r : Type] -> [lres : l -> Type] -> [rres : r -> Type] -> [res : Type] ->
  ((o : l) -> (lres o -> res) -> res) -> ((o : r) -> (rres o -> res) -> res) ->
  (o : Plus l r) -> (PlusRes lres rres o -> res) -> res
handlePlus fl fr (L o) k = fl o k
handlePlus fl fr (R o) k = fr o k

-- A computation that performs nothing is just its result.
runPure : [a : Type] -> Comp NoOp NoRes a -> a
runPure (Done x)       = x
runPure (Call () rest)

-- Partial computations (docs/proposals/partial.md)

-- A recursion request: run the definition being defined again on `x`. A
-- partial definition's body makes these instead of calling itself.
type Rec (req : Type) : Type =
  | Recur (x : req)

-- What a request is answered with.
RecRes : [req : Type] -> (req -> Type) -> Rec req -> Type
RecRes ans (Recur x) = ans x

-- A computation that may not finish: what `{Partial | e} a` stands for.
-- These have no definitions, and nothing can look inside a `Delay`: only
-- the runtime runs one, a step at a time. The kernel admits them as
-- primitives, after checking their types are exactly these.
Delay : (op : Type) -> (res : op -> Type) -> Type -> Type

-- Finished, with this result.
now : [op : Type] -> [res : op -> Type] -> [a : Type] -> a -> Delay op res a

-- A computation that finishes, as one that might not.
lift : [op : Type] -> [res : op -> Type] -> [a : Type] -> Comp op res a -> Delay op res a

-- Sequencing.
bindD : [op : Type] -> [res : op -> Type] -> [a b : Type] ->
  Delay op res a -> (a -> Delay op res b) -> Delay op res b

-- Moves a computation along a mapping between signatures.
mapSig : [op1 : Type] -> [res1 : op1 -> Type] -> [op2 : Type] -> [res2 : op2 -> Type] -> [a : Type] ->
  SigMap op1 res1 op2 res2 -> Delay op1 res1 a -> Delay op2 res2 a

-- The recursive function a description defines: each `Recur y` its body
-- requests is answered by running the body on `y`.
pfix : [op : Type] -> [res : op -> Type] -> [req : Type] -> [ans : req -> Type] ->
  ((x : req) -> Delay (Plus (Rec req) op) (PlusRes (RecRes ans) res) (ans x)) ->
  (x : req) -> Delay op res (ans x)

-- Input and output (docs/proposals/text-and-io.md, Part 2)

-- The console. Only a host interpreter performs these for real; in Stitchwort
-- code, `simulate` interprets them as data.
ability IO where
  print    : Text -> {IO} ()          -- writes the text, then a line ending
  readLine : () -> {IO} (Maybe Text)  -- Nothing only at end of input

-- The first line of scripted input, if there is one.
nextLine : List Text -> Maybe Text
nextLine Nil         = Nothing
nextLine (Cons l ls) = Just l

-- Runs a program against scripted input lines: each `readLine` takes the
-- next one, and gives `Nothing` once they're used up. Records each `print`
-- payload, in order, with the result. A payload is one entry even if it
-- contains a line feed: a real interpreter writes each payload followed by
-- a line ending. The payloads are collected in reverse and turned round at
-- the end, so a long run doesn't build a deep chain of pending pairs.
simulate : List Text -> (() -> {IO | e} a) -> {e} Pair (List Text) a
simulate input prog =
  let run : List Text -> List Text -> {e} Pair (List Text) a =
    handle prog () with
      | return x        -> \ins out -> MkPair (reverseOnto out Nil) x
      | print t => k    -> \ins out -> k () ins (Cons t out)
      | readLine u => k -> \ins out -> k (nextLine ins) (tailOf ins) out
  run input Nil
