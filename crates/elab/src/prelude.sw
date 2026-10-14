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

decEqNat : (m : Nat) -> (n : Nat) -> Decidable (m = n)
decEqNat Zero     Zero     = Yes rfl
decEqNat Zero     (Succ n) = No (zeroNotSucc n)
decEqNat (Succ m) Zero     = No (succNotZero m)
decEqNat (Succ m) (Succ n) = decSucc m n (decEqNat m n)

decNot : [p : Prop] -> Decidable p -> Decidable (Not p)
decNot (Yes h) = No (\n -> n h)
decNot (No r)  = Yes r

decLessEq : (m : Nat) -> (n : Nat) -> Decidable (m <= n)
decLessEq m n = decTrue (leq m n)

decLessThan : (m : Nat) -> (n : Nat) -> Decidable (m < n)
decLessThan m n = decTrue (leq (Succ m) n)

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
