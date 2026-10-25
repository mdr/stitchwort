-- `&&`, `||` and `not`. On `Bool`s they short-circuit: `a && b` is
-- `if a then b else False`, `a || b` is `if a then True else b`. Each operand
-- may also be a decidable proposition (`x < y`), decided as in `if`. Where a
-- proposition is expected they are `And`, `Or` and `Not`.
-- Precedence: `->` < `||` < `&&` < comparisons; both are right-associative.

import Std (List)

-- Bool operands, with a comparison as an operand.
def between (x: Nat) (y: Nat) (z: Nat): Bool := x < y && y < z

test "between" := between 1 2 3
test "not between" := not (between 1 3 2)

-- `&&` binds tighter than `||`, and a chain groups to the right.
test "bools" := True && (False || True)
test "prec: and before or" := False && False || True
test "prec: or after and" := True || False && False
test "right assoc" := True && True && True && not False

-- A bare decidable proposition is a test too.
test "prop test" := 1 < 2 && 2 < 3
test "not prop" := not (3 < 2)
test "or prop" := 3 < 2 || 2 < 3

-- `if` on a conjunction, with and without a proof name.
def pick (x: Nat) (y: Nat): Nat := if x < y && y < 10 then 1 else 2

test "pick, both" := pick 1 2 == 1
test "pick, second fails" := pick 3 20 == 2
test "pick, first fails" := pick 3 2 == 2

def withProof (x: Nat) (y: Nat): Nat := if h: x < y && y < 10 then 1 else 2

test "withProof" := withProof 1 2 == 1 && withProof 5 2 == 2

-- `not` on a proposition.
def notSmall (x: Nat): Nat := if not (x < 5) then 1 else 0

test "notSmall" := notSmall 7 == 1 && notSmall 3 == 0

-- Integers: the operands decide the type of the comparison.
def outside (x: Int): Bool := x < 0 || 100 < x

test "outside" := outside (-3) && outside 101 && not (outside 5)

-- Mixed Bool and comparison operands.
def mixed (b: Bool) (x: Nat): Bool := b && x < 3

test "mixed, true" := mixed True 2
test "mixed, false bool" := not (mixed False 2)
test "mixed, false prop" := not (mixed True 5)

-- A Bool in a `let`, then used as a condition.
def letted (x: Nat): Nat :=
  let b := x < 3 && 1 < x
  if b then 1 else 0

test "letted" := letted 2 == 1 && letted 5 == 0

def chain (x: Nat): Bool := 0 < x && x < 10 && x != 5 || x == 100

test "chain" := chain 3 && chain 100 && not (chain 5) && not (chain 0)

-- The right side knows the left side, as in `if a then b else False`: the
-- `%` and `/` need a proof that `n != 0`, found from the left operand (the
-- AoC 2025 day 2 guard). A `Bool` left side (`n == 0`) says nothing, just as
-- `if n == 0` doesn't.
def repeatsEvery (len: Nat) (n: Nat): Bool := n != 0 && len % n == 0

test "repeatsEvery" := repeatsEvery 6 3 && not (repeatsEvery 6 0) && not (repeatsEvery 6 4)

-- In `a || b`, `b` knows `Not a`.
def bigShare (total: Nat) (n: Nat): Bool := n = 0 || total / n > 2

test "bigShare" := bigShare 10 0 && bigShare 10 3 && not (bigShare 10 5)

-- In a chain `a && b && c`, `c` knows both `a` and `b`.
def bothDivide (a: Nat) (b: Nat) (c: Nat): Bool := a != 0 && b != 0 && c % a + c % b == 0

test "bothDivide" := bothDivide 2 3 6 && not (bothDivide 0 3 6) && not (bothDivide 4 3 6)

-- `not` is an ordinary function on `Bool` as well.
def flipped: List Bool := List.map [True, False] not

test "not as a function" := flipped == [False, True]

-- Proofs: in a type, `&&` is `And` (constructor `Both`) and `||` is `Or`
-- (constructors `Inl`, `Inr`).
theorem andComm (p: Prop) (q: Prop): p && q -> q && p
  | Both a b => Both b a

theorem swapOr (p: Prop) (q: Prop): p && q -> q || p
  | Both a b => Inl b

theorem literal: 1 < 2 && 2 < 3 := Both rfl rfl

-- Short-circuiting: the right operand's effects run only when needed.
ability Log where
  say: Nat -> {Log} ()

def collect (prog: () -> {Log | e} a): {e} Pair (List Nat) a :=
  handle prog() with
    | return x => MkPair Nil x
    | say n, k =>
      let rest := k()
      MkPair (Cons n (rest.fst)) (rest.snd)

def noisy (n: Nat) (b: Bool): {Log} Bool :=
  say n
  b

def andSkips(): {Log} Bool := noisy 1 False && noisy 2 True
def andRuns(): {Log} Bool := noisy 1 True && noisy 2 True
def orSkips(): {Log} Bool := noisy 1 True || noisy 2 False
def orRuns(): {Log} Bool := noisy 1 False || noisy 2 True
def pureLeft (x: Nat): {Log} Bool := x < 3 && noisy 2 True
def notEff(): {Log} Bool := not (noisy 7 False)
def inIf(): {Log} Nat := if noisy 1 False && noisy 2 True then 1 else 0
-- With effects on the right too, the right side knows the left.
def guarded (n: Nat): {Log} Bool := n != 0 && noisy (10 / n) True

test "and skips the right" := (collect andSkips) == ([1], False)
test "and runs the right" := (collect andRuns) == ([1, 2], True)
test "or skips the right" := (collect orSkips) == ([1], True)
test "or runs the right" := (collect orRuns) == ([1, 2], True)
test "pure left false" := (collect (u => pureLeft 5)) == ([], False)
test "pure left true" := (collect (u => pureLeft 1)) == ([2], True)
test "not keeps the effect" := (collect notEff) == ([7], True)
test "in if" := (collect inIf) == ([1], 0)
test "guarded, zero" := (collect (u => guarded 0)) == ([], False)
test "guarded, five" := (collect (u => guarded 5)) == ([2], True)
