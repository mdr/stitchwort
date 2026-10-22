-- core/Data.sw. The core data types: `Nat` and its arithmetic, `Bool`,
-- `List`, `Option`, `Pair`, and the first list functions. Loaded with the
-- core: The registry's built-ins are these types and their operations,
-- `Bool.True`/`False` are written by name, and the runner uses `Pair.fst`
-- (docs/proposals/prelude-slim.md §2.1).

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
type Option (a: Type): Type =
  | None
  | Some (value: a)

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

