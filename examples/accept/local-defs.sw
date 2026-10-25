-- Local definitions in blocks. A `def` or `theorem` may stand wherever a
-- `let` may; the elaborator lifts it to a top-level definition `owner.name`
-- that takes the variables it uses as leading parameters (docs/syntax.md,
-- "Local definitions"). The cases below: recursion, groups, captures of every
-- kind, lemmas, nesting, scoping, and naming from outside.

-- A recursive helper with an accumulator, next to a plain `let`.
def sumTo (n: Nat): Nat :=
  let start := 0
  def go: Nat → Nat → Nat
    | Zero, acc => acc
    | Succ k, acc => go k (acc + Succ k)
  go n start

test "sumTo" := sumTo 4 == 10

-- A group: consecutive local definitions are mutually recursive, and the
-- first one may use the second. `offset` is captured by `second`, and so
-- by `first`.
def outer (offset: Nat): Nat :=
  def first (x: Nat): Nat := second x
  def second (x: Nat): Nat := offset + x
  first 3

test "outer" := outer 4 == 7

def evenOdd (n: Nat): Bool :=
  def isEven: Nat → Bool
    | Zero => True
    | Succ k => isOdd k
  def isOdd: Nat → Bool
    | Zero => False
    | Succ k => isEven k
  isEven n

test "evenOdd" := evenOdd 10

-- A lemma about a local helper, and the body uses it. The helper doesn't
-- call its owner, so it is final in time for the lemma's type to compute.
def sumTo2 (n: Nat): Nat :=
  def go: Nat → Nat → Nat
    | Zero, acc => acc
    | Succ k, acc => go k (acc + Succ k)
  theorem goZero (a: Nat): go 0 a = a := rfl
  let r := go n 0
  r

test "sumTo2" := sumTo2 4 == 10

-- Implicit capture: the element type stays an implicit parameter of
-- `count.go`, so recursion on a smaller list is accepted as at top level.
def count [a: Type] (xs: List a) (p: a → Bool): Nat :=
  def go: List a → Nat
    | Nil => 0
    | Cons x rest => if p x then Succ (go rest) else go rest
  go xs

test "count" := count [1, 2, 3, 4] (== 2) == 1

def need (i: Nat) (ok: i < 5): Nat := i

-- Dependent capture: the proof `ok` mentions `i`, so both are captured.
def safe (i: Nat) (ok: i < 5): Nat :=
  def get (extra: Nat): Nat := need i ok + extra
  get 1

test "safe" := safe 2 rfl == 3

def needAuto (i: Nat) [auto ok: i < 5]: Nat := i

-- Auto evidence: the local definition calls a function that needs it. The
-- evidence is captured, as an `auto` parameter of the lifted definition.
def useAuto (i: Nat) [auto ok: i < 5]: Nat :=
  def get (extra: Nat): Nat := needAuto i + extra
  get 1

test "auto" := useAuto 2 == 3

-- Recursion between a local definition and its owner.
def ping (n: Nat): Nat :=
  def pong: Nat → Nat
    | Zero => 0
    | Succ k => ping k
  match n with
    | Zero => 0
    | Succ k => pong k

test "ping" := ping 5 == 0

-- Nested blocks: a definition inside a definition.
def nested (n: Nat): Nat :=
  def double (x: Nat): Nat :=
    def twice (y: Nat): Nat := y + y
    twice x
  double (double n)

test "nested" := nested 3 == 12

-- From outside, a local definition is named `owner.name`, and a nested one
-- `owner.name.inner`.
theorem sumToGo (a: Nat): sumTo.go 0 a = a := rfl

def usesNested: Nat := nested.double.twice 4

test "usesNested" := usesNested == 8

-- In an arm, capturing a pattern variable.
def addAll: List Nat → Nat → Nat
  | Nil, n => n
  | Cons x rest, n =>
    def plusX (m: Nat): Nat := m + x
    plusX (addAll rest n)

test "arm" := addAll [1, 2, 3] 4 == 10

-- Inside a `match` alternative.
def inMatch (n: Nat) (m: Nat): Nat :=
  1 + match n with
    | Zero => 0
    | Succ k =>
      def times (j: Nat): Nat := j * m
      times k

test "inMatch" := inMatch 3 5 == 11

-- A `match` inside a local definition.
def withMatch (xs: List Nat): Nat :=
  def go: List Nat → Nat
    | Nil => 0
    | Cons x rest => 2 * (match x with
      | Zero => 1
      | Succ _ => go rest)
  go xs

test "withMatch" := withMatch [1, 2, 0] == 8

-- Shadowing both ways: the definition shadows the parameter `go`, and a
-- later `let` shadows the definition.
def shadow (go: Nat): Nat :=
  def go (x: Nat): Nat := x + 1
  let r := go 1
  let go := 10
  r + go

test "shadow" := shadow 100 == 12

-- In a test.
test "local in test" :=
  def three: Nat := 3
  three == 3

-- In a condition: `if`, `&&`, `||` and `not` with local definitions, which
-- are lifted after the body, so the condition is elaborated again once they
-- are.
def classify (x: Nat): Nat :=
  def double (y: Nat): Nat := y + y
  def small: Nat := 3
  if double 2 == 4 ∧ (double x < small ∧ not (double x == 0) ∨ x == 10) then 1 else 0

test "classify" := classify 1 == 1 ∧ classify 0 == 0 ∧ classify 2 == 0 ∧ classify 10 == 1

test "local in test with &&" :=
  def double (y: Nat): Nat := y + y
  double 2 == 4 ∧ not (double 1 == 3)

-- A `count`-style accumulator: termination is checked on the lifted helper.
-- (The long run, as a JS loop, is in examples/extract/local-defs.sw: the
-- differential test evaluates every example test with the recursive
-- reference evaluator too.)
def loop (n: Nat): Nat :=
  def count: Nat → Nat → Nat
    | Zero, acc => acc
    | Succ k, acc => count k (Succ acc)
  count n 0

test "loop" := loop 1000 == 1000
