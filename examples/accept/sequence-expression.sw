-- A sequence expression `(a; b)` runs `a`, then gives `b`'s value (SW-888,
-- D1700). It is the block's two lines `a` and `b` written on one line, with
-- the same tree, so `a`'s value is dropped as a block line's is, its effects
-- happen first, and `let` mixes in: `(a; let x := e; b)`. Like an
-- expression `let`, it runs as far as an expression can, and ends at a
-- comma or a closing bracket.

import Std (Bool, Fail, List, Nat, Option, Parse, Result, Text)
import Std.Parse (before, char, findAll, nat, natDigits, oneOf, pick, text)

-- The value is the last part's.
def pair: Nat := (1; 2)

def chain: Nat := (1; 2; 3)

test "the last value" := pair == 2 && chain == 3

-- Nested, and as arguments: each pair of brackets is one sequence.
def nested: Nat := ((1; 2); (3; 4))

def add (a: Nat) (b: Nat): Nat := a + b

def arguments: Nat := add (0; 1) (0; 2)

test "nested and as arguments" := nested == 4 && arguments == 3

-- With `let`, on either side: a `let`'s body may be a sequence, and a
-- sequence may go on with a `let`.
def letFirst: Nat := (let x := 1; 5; x + 1)

def letAfter: Nat := (5; let x := 1; 6; x + 2)

-- A `;` straight after a `let`'s value ends the value, so these are lets
-- with bodies, not sequences inside the values.
def lambdaValue: Nat := (let f := (n: Nat) => n + 1; f 2)

def ifValue (b: Bool): Nat := (let y := if b then 1 else 2; y + 10)

test "with let" := letFirst == 2 && letAfter == 3 && lambdaValue == 3 && ifValue True == 11

-- After `:=`, `=>`, `then` and `else`, it runs as far as an expression can,
-- as an expression `let`'s body does.
def lambdas: List Nat := [1, 2].map (x => 0; x + 1)

def branches (b: Bool): Nat := if b then 0; 1 else 2; 3

def arms (o: Option Nat): Nat :=
  match o with
    | Some k => 0; k
    | None => 1; 2

test "positions" := lambdas == [2, 3] && branches True == 1 && branches False == 3 && arms (Some 5) == 5 && arms None == 2

-- It ends at a comma, so `(1; 2, 3)` is the pair `((1; 2), 3)`, and at the
-- end of a `|>` stage's operand it takes the whole stage: `0; 1 |> f` is
-- `0; (1 |> f)`.
def tuple: (Nat, Nat) := (1; 2, 3)

def items: List Nat := [1; 2, 3; 4]

def piped: Nat := 0; 1 |> (n => n + 1)

test "commas and pipes" := tuple == (2, 3) && items == [2, 4] && piped == 2

-- Effects run in order, the first part's before the rest. A one-line
-- definition may be a sequence.
def lineResult (line: Text) (parser: () → {Parse} a): Result a Text := Fail.toResult (() => Parse.line line parser)

def afterComma(): {Parse} Nat := char ','; nat()

test "effects in order" := lineResult ",12" afterComma == Ok 12 && lineResult "12" afterComma == Err "column 1: expected ',', got '1'"

-- The motivating use: a grammar rule on one line. `before` reads ")" after
-- `|>`'s left side has run.
type Instruction =
  | Mul (left: Nat) (right: Nat)
  | Do
  | Dont

def shortNumber(): {Parse} Nat := natDigits 1 3

def mul(): {Parse} Instruction := Mul (text "mul("; shortNumber()) (char ','; shortNumber()) |> before ")"

-- The same rule in blocks.
def mulBlocks(): {Parse} Instruction :=
  text "mul("
  let left := shortNumber()
  char ','
  let right := shortNumber()
  char ')'
  Mul left right

test "a grammar rule" :=
  lineResult "mul(44,46)" mul == Ok (Mul 44 46) && lineResult "mul(44;46)" mul == lineResult "mul(44;46)" mulBlocks
    && lineResult "mul(44,46]" mul == lineResult "mul(44,46]" mulBlocks

def instruction(): {Parse} Instruction :=
  oneOf [
    () => Mul (text "mul("; shortNumber()) (char ','; shortNumber()) |> before ")",
    () => pick [("do()", Do), ("don't()", Dont)]
  ]

test "in context" :=
  Fail.toResult (() => Parse.all "xmul(2,4)%don't()_mul(5,5)+mul(32,64]do()mul(11,8)" (() => findAll instruction))
    == Ok [Mul 2 4, Dont, Mul 5 5, Do, Mul 11 8]

-- The tree is the block's, so the checker sees the two forms as equal.
def oneLine (n: Nat): Nat := (n; n + 1)

def twoLines (n: Nat): Nat :=
  n
  n + 1

theorem sameAsBlock (n: Nat): oneLine n = twoLines n := rfl
