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
-- `leq`, `eqNat`, `divFuel` and `decEqNat` also have native implementations,
-- used when all their arguments are numbers; they're tested against the
-- definitions here.
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

-- Whether two numbers are equal, as a `Bool`.
eqNat : Nat -> Nat -> Bool
eqNat Zero     Zero     = True
eqNat Zero     (Succ n) = False
eqNat (Succ m) Zero     = False
eqNat (Succ m) (Succ n) = eqNat m n

theorem eqNatRefl : (n : Nat) -> eqNat n n = True
eqNatRefl Zero     = rfl
eqNatRefl (Succ n) = eqNatRefl n

-- Numbers that `eqNat` says differ are different. The native `decEqNat`
-- builds its `No` from this.
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

decEqNat : (m : Nat) -> (n : Nat) -> Decidable (m = n)
decEqNat Zero     Zero     = Yes rfl
decEqNat Zero     (Succ n) = No (zeroNotSucc n)
decEqNat (Succ m) Zero     = No (succNotZero m)
decEqNat (Succ m) (Succ n) = decSucc m n (decEqNat m n)

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
