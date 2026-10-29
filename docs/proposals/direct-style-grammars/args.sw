-- Evidence for docs/proposals/direct-style-grammars.md §2: effectful calls
-- in argument position, the order they run in, and what the parser accepts.
--
--   $ stitchwort test docs/proposals/direct-style-grammars/args.sw

import Std (Char, Fail, List, Nat, Parse, Result, Text)
import Std.Parse (char, natDigits, text)

type Instruction =
  | Mul (left: Nat) (right: Nat)

type Two =
  | MkTwo (first: Char) (second: Char)

def shortNumber(): {Parse} Nat := natDigits 1 3

def any(): {Parse} Char := Parse.satisfy "a character" (_ => True)

def lineResult (line: Text) (parser: () → {Parse} a): Result a Text := Fail.toResult (() => Parse.line line parser)

-- A constructor's arguments run left to right.
def twoArgs(): {Parse} Two := MkTwo (any()) (any())

test "arguments run left to right" := lineResult "ab" twoArgs == Ok (MkTwo 'a' 'b')

-- So do a tuple's parts.
def twoParts(): {Parse} (Char, Char) := (any(), any())

test "tuple parts run left to right" := lineResult "ab" twoParts == Ok ('a', 'b')

-- And a list's items.
def threeItems(): {Parse} (List Char) := [any(), any(), any()]

test "list items run left to right" := lineResult "abc" threeItems == Ok ['a', 'b', 'c']

-- And a record's fields, as written.
type Pair = { x: Char, y: Char }

def recordFields(): {Parse} Pair := { y = any(), x = any() }

test "record fields run as written" := lineResult "ab" recordFields == Ok ({ x = 'b', y = 'a' })

-- Day 3's rule with today's expression `let` for the separator.
def letExpr(): {Parse} Instruction :=
  text "mul("
  let m := Mul (shortNumber()) (let _ := char ','; shortNumber())
  char ')'
  m

test "let expression" := lineResult "mul(44,46)" letExpr == Ok (Mul 44 46)

test "let expression: a bad separator" := lineResult "mul(44;46)" letExpr == Err "column 7: expected ',', got ';'"

-- `let () :=` works too, and says the value is `()`.
def letUnit(): {Parse} Instruction :=
  text "mul("
  let m := Mul (shortNumber()) (let () := char ','; shortNumber())
  char ')'
  m

test "let unit" := lineResult "mul(1,2)" letUnit == Ok (Mul 1 2)

-- All of it in one expression.
def oneLine(): {Parse} Instruction :=
  (let () := text "mul("; let m := Mul (shortNumber()) (let () := char ','; shortNumber()); let () := char ')'; m)

test "one line" := lineResult "mul(1,2)" oneLine == Ok (Mul 1 2)

-- A block may start on a new line inside brackets, as an argument.
def bracketBlock(): {Parse} Instruction :=
  Mul
    (shortNumber())
    (
      char ','
      shortNumber()
    )

test "a block in brackets" := lineResult "1,2" bracketBlock == Ok (Mul 1 2)

-- A statement's value need not be `()`: it is dropped.
def dropped(): {Parse} Nat :=
  shortNumber()
  char ','
  shortNumber()

test "a dropped value" := lineResult "1,2" dropped == Ok 2

-- A pure function sequences too, since its arguments run before it is
-- called, even the one it ignores.
def drop (ignored: ()) (value: a): a := value

def viaDrop(): {Parse} Instruction := Mul (drop (text "mul(") (shortNumber())) (drop (char ',') (shortNumber()))

test "via drop" := lineResult "mul(1,2" viaDrop == Ok (Mul 1 2)

-- Named arguments run where they are written, not in parameter order.
def pair (first: Nat) (second: Nat): (Nat, Nat) := (first, second)

def named(): {Parse} (Nat, Nat) := pair (second := shortNumber()) (first := (let () := char ','; shortNumber()))

test "named arguments run as written" := lineResult "1,2" named == Ok (2, 1)
