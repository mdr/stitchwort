-- List spreads: `[a, b, ..xs]` is `Cons a (Cons b xs)`. A `..` can come in
-- any position, any number of times: `[..xs, y]` is `xs ++ [y]` and
-- `[a, ..xs, b, ..ys]` is `Cons a (xs ++ Cons b ys)` (docs/proposals/list-spread.md).
-- A final spread is a plain `Cons` chain, so `rfl` sees through it.

def front (xs: List Nat): List Nat := [1, 2, ..xs]

test "front" := front [3, 4] == [1, 2, 3, 4]

theorem frontIsCons ∀ (xs: List Nat): front xs = [1, 2, ..xs] := rfl

-- Equations step through a spread as through `Cons`.
def total: List Nat → Nat
  | [] => 0
  | [x, ..rest] => x + total rest

theorem totalCons ∀ (x: Nat) (xs: List Nat): total [x, ..xs] = x + total xs := rfl

-- `[..xs]` is `xs`.
theorem justSpread ∀ (xs: List Nat): [..xs] = xs := rfl

-- A spread's tail is any expression up to the `]`.
def joined (xs ys: List Nat): List Nat := [0, ..xs ++ ys]

test "joined" := joined [1] [2] == [0, 1, 2]

-- Anywhere, and more than once.
def snoc (xs: List Nat) (y: Nat): List Nat := [..xs, y]

theorem snocIsAppend ∀ (xs: List Nat) (y: Nat): snoc xs y = xs ++ [y] := rfl

def both (xs ys: List Nat): List Nat := [..xs, ..ys]

theorem bothIsAppend ∀ (xs ys: List Nat): both xs ys = xs ++ ys := rfl

def mixed (xs ys: List Nat): List Nat := [1, ..xs, 2, ..ys]

theorem mixedIsAppendCons ∀ (xs ys: List Nat): mixed xs ys = [1, ..xs ++ [2, ..ys]] := rfl

test "mixed" := mixed [10, 11] [20] == [1, 10, 11, 2, 20]

-- The element type can come from the spread.
def inferred (xs: List Int): List Int := [1, ..xs]

test "inferred" := inferred [2] == [1, 2]

-- Patterns and expressions read alike.
def swapFirstTwo: List Nat → List Nat
  | [a, b, ..rest] => [b, a, ..rest]
  | other => other

test "swapFirstTwo" := swapFirstTwo [1, 2, 3] == [2, 1, 3]

-- Abilities in elements and spreads run left to right, as written.
ability Log where
  say: Nat → {Log} ()

def loud (n: Nat): {Log} List Nat :=
  say n
  [n]

def order(): {Log} List Nat := [..loud 1, 9, ..loud 2]

def sayAll (prog: () → {Log | e} a): {e} List Nat :=
  handle prog() with
    | return x => []
    | say n, k => [n, ..k()]

test "abilities run in order" := sayAll order == [1, 2]

-- A long literal with a spread still works.
def long (xs: List Nat): List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, ..xs]

test "long" := (long [10]).length == 11
