-- `then` and `else` can start a line, at the column of the `if`'s own line
-- or further in, so `if` chains read top to bottom.

def sign (n: Nat): Nat :=
  if n == 0 then 0
  else 1

def grade (n: Nat): Nat :=
  if n == 0 then 10
  else if n == 1 then 20
  else if n == 2 then 30
  else 40

-- `then` on its own line too, and branches that are blocks.
def describe (n: Nat): Nat :=
  if n == 0
  then 100
  else
    let m := n + 1
    m * 2

-- Nested: the inner chain's `else` belongs to the inner `if`.
def nested (a: Nat) (b: Nat): Nat :=
  if a == 0 then
    if b == 0 then 1
    else 2
  else
    if b == 0 then 3
    else 4

-- Inside `let`, with `else` lined up under the `let`.
def inLet (n: Nat): Nat :=
  let x := if n == 0 then 5
  else 6
  x + 1

-- With a proof binder.
def safeDiv (n: Nat) (d: Nat): Nat :=
  if h: d != 0 then n / d
  else 0

-- In handler clauses.
ability Say where
  say: Nat -> {Say} ()

def withHandler (n: Nat): Nat :=
  handle say n with
    | return x      => if n == 0 then 7
                       else 8
    | say m, k    => if m == 0 then 9
                       else if m == 1 then 10
                       else 11

-- Indented `else` still works.
def indented (n: Nat): Nat :=
  if n == 0 then 1
    else 2

test "sign" := sign 0 == 0
test "sign of a positive" := sign 5 == 1
test "grade" := grade 1 == 20
test "grade, last branch" := grade 9 == 40
test "describe" := describe 0 == 100
test "describe, block branch" := describe 4 == 10
test "nested" := nested 0 1 == 2
test "nested, outer else" := nested 1 0 == 3
test "inLet" := inLet 0 == 6
test "safeDiv" := safeDiv 6 3 == 2
test "safeDiv, zero" := safeDiv 6 0 == 0
test "withHandler" := withHandler 0 == 9
test "withHandler, else if" := withHandler 1 == 10
test "withHandler, last else" := withHandler 5 == 11
test "indented" := indented 1 == 2
