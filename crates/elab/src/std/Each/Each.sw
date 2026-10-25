-- `Each`: run a computation once for each choice it makes, and collect every
-- result, as Scala's `for`/`yield` or Haskell's list monad do. Code that
-- chooses says `{Each}` in its row, picks an element of a list with `each`,
-- and drops the current choice with `require`. The handler `Each.collect`
-- resumes once per element and joins the results in order.
--
--   def pairs (n: Nat): List (Pair Nat Nat) := Each.collect (() =>
--     let a := each (List.between 1 n)
--     let b := each (List.between a n)
--     require (a + b == n)
--     (a, b))
--
-- `pairs 6` is `[(1, 5), (2, 4), (3, 3)]`. Proofs about a collected
-- computation needn't know about the handler: `Each.collectEach`,
-- `Each.collectRequire` and `Each.collectPure` turn it into
-- `List.flatMap`, `if` and `[v]`.

-- The two operations, as in Koka's and Eff's nondeterminism: `fork` asks
-- for both answers to a yes/no question, and `stop` gives none. They're
-- enough for `each` over a list of any type; an operation can't be
-- polymorphic in the element type (docs/proposals/abilities.md).
ability Each where
  fork: () → {Each} Bool
  stop: () → {Each} Empty

-- Each element of `xs` in turn: the rest of the computation runs once for
-- each. On `[]` it runs no more.
def Each.each: List a → {Each} a
  | [] => Empty.absurd Each.stop()
  | [x, ..xs] => if Each.fork() then x else Each.each xs

-- Keep this choice only if `ok`.
def Each.require (ok: Bool): {Each} () := if ok then () else Empty.absurd Each.stop()

-- Every result, in order: for `each xs`, the results for the first element,
-- then those for the second, and so on.
def Each.collect (prog: () → {Each} a): List a :=
  handle prog() with
    | return x => [x]
    | Each.fork u, k => Each.both (b => k b)
    | Each.stop u, k => []

-- The results for `True`, then those for `False`. `k` is a plain function
-- here, so `collect`'s clause performs nothing and its lemmas compute.
def Each.both (k: Bool → List a): List a := List.append (k True) (k False)

-- The same, inside other abilities, which pass through: each continuation
-- performs them separately (put `Each` innermost for one state per choice,
-- as with `allResults` in `examples/accept/abilities.sw`).
def Each.collectIn (prog: () → {Each | e} a): {e} List a :=
  handle prog() with
    | return x => [x]
    | Each.fork u, k => List.append (k True) (k False)
    | Each.stop u, k => []

-- The bridging lemmas: a collected computation is a `flatMap` over each
-- `each`, an `if` at each `require`, and `[v]` at the end.

-- A value alone gives just that value.
theorem Each.collectPure (v: a): Each.collect (() => v) = [v] := rfl

-- Choosing from `xs`, then running `k` on the choice, collects `k`'s
-- results for each element in turn.
theorem Each.collectEach (k: a → {Each} b): (xs: List a) →
    Each.collect (() => k (Each.each xs)) = List.flatMap xs (x => Each.collect (() => k x))
  | [] => rfl
  | [x, ..xs] => Eq.cong (List.append (Each.collect (u => k x))) (Each.collectEach k xs)

-- `require ok` before `k`: `k`'s results if `ok`, else none.
theorem Each.collectRequire (k: () → {Each} b): (ok: Bool) →
    Each.collect (() =>
      Each.require ok
      k()) = (if ok then Each.collect k else [])
  | True => rfl
  | False => rfl

-- `each` of a list collects to the list itself.
theorem Each.collectEachSelf: (xs: List a) → Each.collect (() => Each.each xs) = xs
  | [] => rfl
  | [x, ..xs] => Eq.cong (Cons x) (Each.collectEachSelf xs)

test "each" := Each.collect (() => Each.each [1, 2, 3]) == [1, 2, 3]
test "each of nothing" := Each.collect (() => Each.each ([]: List Nat)) == []
test "each twice: the first choice varies slowest" :=
  Each.collect (() =>
    let a := Each.each [1, 2]
    let b := Each.each [10, 20]
    a + b) == [11, 21, 12, 22]
test "require drops a choice" :=
  Each.collect (() =>
    let n := Each.each [1, 2, 3, 4, 5, 6]
    Each.require (n % 2 == 0)
    n) == [2, 4, 6]
test "a later choice depends on an earlier one" :=
  Each.collect (() =>
    let a := Each.each [1, 2, 3]
    let b := Each.each (List.between a 3)
    (a, b)) == [(1, 1), (1, 2), (1, 3), (2, 2), (2, 3), (3, 3)]

-- With another ability: the handler outside decides. `Abort` outside
-- `Each` gives up on everything at the first `abort`; inside, only that
-- choice gives up.
test "abort outside each: one abort stops every choice" :=
  Abort.toOption (() => Each.collectIn (() =>
    let n := Each.each [2, 3, 4]
    Abort.ensure (n % 2 == 0)
    n / 2)) == None
test "abort outside each: no abort" :=
  Abort.toOption (() => Each.collectIn (() =>
    let n := Each.each [2, 4]
    Abort.ensure (n % 2 == 0)
    n / 2)) == Some [1, 2]
test "abort inside each: only that choice gives up" :=
  Each.collect (() => Abort.toOption (() =>
    let n := Each.each [2, 3, 4]
    Abort.ensure (n % 2 == 0)
    n / 2)) == [Some 1, None, Some 2]
test "require inside abort inside each" :=
  Each.collect (() =>
    let n := Each.each [1, 2, 3, 4]
    Each.require (n ≠ 3)
    Abort.orElse 0 (() =>
      Abort.ensure (n % 2 == 0)
      n)) == [0, 2, 4]
