--| The core data types: `Nat` and its arithmetic, `Bool`,
--| `List`, `Option`, `Pair`, and the first list functions.
-- Loaded with the core: The registry's built-ins are these types and their
-- operations, `Bool.True`/`False` are written by name, and the runner uses
-- `Pair.fst` (docs/proposals/prelude-slim.md §2.1).

-- Numbers

--| A natural number: 0, 1, 2 and so on, as `Zero` and `Succ` of the number
--| before. Numbers are stored compactly, but mean exactly this. [`Nat.add`], [`Nat.sub`],
--| [`Nat.mul`], [`Nat.leq`], [`Nat.equal`], [`Nat.divFuel`], [`Nat.decEq`],
--| [`Nat.equalRefl`] and [`Nat.equalSound`] also have native implementations, used
--| when all their arguments are numbers. Each computes exactly what the
--| definition here computes, proofs included; they're tested against these
--| definitions.
type Nat: Type = | Zero | Succ (n: Nat)

--| `a + b` means `Nat.add a b`. It recurses on its first argument, so
--| `Succ m + n` computes to `Succ (m + n)`.
def Nat.add: (m: Nat) → (n: Nat) → Nat
  | Zero, n => n
  | Succ m, n => Succ (Nat.add m n)

--| `a - b`, stopping at zero: `3 - 5 = 0`.
@[tailrec]
def Nat.sub: (m: Nat) → (n: Nat) → Nat
  | m, Zero => m
  | Zero, Succ n => Zero
  | Succ m, Succ n => Nat.sub m n

--| `a * b`: multiplication of numbers.
def Nat.mul: (m: Nat) → (n: Nat) → Nat
  | Zero, n => 0
  | Succ m, n => n + Nat.mul m n

--| The number before `n`, and 0 for 0.
def Nat.pred: (n: Nat) → Nat
  | Zero => Zero
  | Succ n => n

-- Booleans

--| `True` or `False`: what a test computes, and what `if` branches on.
type Bool: Type = | False | True

--| The opposite of `b`: `True` for `False` and `False` for `True`.
def Bool.not: (b: Bool) → Bool
  | False => True
  | True => False

--| `if c then a else b`. The branches take a (unused) proof of `Unit` so that
--| only the chosen one is evaluated.
def Bool.ifThenElse: [a: Type] → (cond: Bool) → (ifTrue: Unit → a) → (ifFalse: Unit → a) → a
  | True, thenBranch, elseBranch => thenBranch Trivial
  | False, thenBranch, elseBranch => elseBranch Trivial

--| Whether `m <= n`, as a `Bool`.
@[tailrec]
def Nat.leq: (m: Nat) → (n: Nat) → Bool
  | Zero, n => True
  | Succ m, Zero => False
  | Succ m, Succ n => Nat.leq m n

--| `m <= n` as a proposition, defined by computation: `Nat.leq m n` is `True`.
def Nat.LessEq (m n: Nat): Prop := Nat.leq m n = True

--| `m < n` as a proposition, defined by computation: `m + 1 <= n`.
def Nat.LessThan (m n: Nat): Prop := Nat.leq (Succ m) n = True

-- Lists

--| A sequence of values of one type: `[1, 2, 3]` is `Cons 1 (Cons 2 (Cons 3 Nil))`.
type List (a: Type): Type = | Nil | Cons (head: a) (tail: List a)

--| `n` plus the length of `xs`, counted in a loop. The runtimes run it for
--| [`List.length`], so a long list doesn't run out of stack
--| (`List.lengthOntoEq` proves them equal).
@[tailrec]
def List.lengthOnto: (xs: List a) → (acc: Nat) → Nat
  | [], n => n
  | [x, ..xs], n => List.lengthOnto xs (Succ n)

--| The number of elements: `[5, 6, 7].length` is 3. O(n), counted in
--| a loop, so a long list doesn't run out of stack (`List.lengthOntoEq`).
-- `a` is bound automatically, as an implicit argument: `List.length: [a: Type] -> ...`.
def List.length: (xs: List a) → Nat
  | [] => 0
  | [x, ..xs] => Succ (List.length xs)

--| `xs ++ ys`: the elements of `xs`, then those of `ys`. Costs the length of
--| `xs`, not of `ys`; `List.concat` joins many lists, `List.flatMap` maps then joins.
def List.append: (xs: List a) → (ys: List a) → List a
  | [], ys => ys
  | [x, ..xs], ys => [x, ..List.append xs ys]

--| A value that may be missing.
type Option (a: Type): Type = | None | Some (value: a)

--| Two values together, of any two types: `(1, "a")`. Its fields' accessors, [`Pair.fst`] and [`Pair.snd`], are
--| generated.
type Pair (a: Type) (b: Type): Type = | MkPair (fst: a) (snd: b)

--| `List.reverseOnto xs acc` is `xs` reversed, followed by `acc`; `acc` is the
--| accumulator, so a loop can build the result in reverse. Tail-recursive, O(n).
@[tailrec]
def List.reverseOnto: (xs: List a) → (acc: List a) → List a
  | [], acc => acc
  | [x, ..xs], acc => List.reverseOnto xs [x, ..acc]
