--| `shaped` is the parser's shape: it holds of what the parser gives in slice 1, and refuses trees the parser never
--| builds whose printed text reads back as another tree (SW-4069).

namespace Fmt.Tests
import Fmt (..)
import Std (Bool, List, Option, Result, Text)
import Syntax (Comments, Expr, InfixKind, Note, SourceFile, Tok, Word, lex, parseFile)

--| A source parses, from the leaves `parse1` reads, to a file within slice 1 that is `shaped`.
def parsesShaped (source: Text): Bool := match lex source with
  | Err _ => False
  | Ok lexed =>
    match parseFile lexed.settledOnce with
      | Err _ => False
      | Ok file => file.within1 && file.shaped

def bare (text: Text): Word := fixedWord text Comments.none

def name (text: Text): Expr := Atom Lower (bare text)

def number (text: Text): Expr := Atom Num (bare text)

def binary (left: Expr) (operator: Text) (right: Expr): Expr := Infix InfixBinary left (bare operator) right

def sign (operator: Text) (operand: Expr): Expr := Prefix (bare operator) operand

--| Within slice 1, and refused by `shaped`.
def refused (expr: Expr): Bool := expr.within1 && !expr.shaped

--| Within slice 1, and `shaped`.
def accepted (expr: Expr): Bool := expr.within1 && expr.shaped

test "shaped1 holds of the parse of calls with signed arguments and a negative numeral as head" :=
  parsesShaped "def x: Nat := f -x !b -1 (a, b) [1] - 2 * 3 + -4 n\n"

test "shaped1 holds of the parse of chains nesting each way" :=
  parsesShaped "def y: A -> B -> C := a - b - c ++ d ++ e * f % g && h || i\n"

test "shaped1 holds of the parse of signs at the unary level" := parsesShaped "def z: Bool := !f x && - -y == -(1 n)\n"

test "shaped1 refuses a subtraction nested to the right, which prints as `a - b - c`" :=
  refused (binary (name "a") "-" (binary (name "b") "-" (name "c")))

test "shaped1 accepts the subtraction nested to the left" :=
  accepted (binary (binary (name "a") "-" (name "b")) "-" (name "c"))

test "shaped1 refuses a call whose head is `!` on a name, which prints as `!x y`" :=
  refused (App (sign "!" (name "x")) [name "y"])

test "shaped1 refuses a call whose head is `-` on a name, which prints as `-x y`" :=
  refused (App (sign "-" (name "x")) [name "y"])

test "shaped1 accepts a call whose head is a negative numeral, `-1 n`" :=
  accepted (App (sign "-" (number "1")) [name "n"])

test "shaped1 refuses a call whose head is `!` on a numeral, which prints as `!1 n`" :=
  refused (App (sign "!" (number "1")) [name "n"])

test "shaped1 refuses an argument that is a sign on a sign, which prints as `f - -x`" :=
  refused (App (name "f") [sign "-" (sign "-" (name "x"))])

test "shaped1 accepts an argument that is a sign on an atom, `f -x`" := accepted (App (name "f") [sign "-" (name "x")])

-- Comments on a glued sign (SW-4081): `callArgument` and `callHead` ask `signQuiet`.

--| `-` with a comment after it.
def noisyMinus: Word := fixedWord "-" { Comments.none | after = Some "-- c" }

test "shaped1 holds of the parse of glued signs, and of comments on signs that aren't glued" :=
  parsesShaped "def x: Nat := f -x !b -1 (- -- c\n  1) (! -- b\n  y) - -- d\n  2 + -4 n\n"

test "shaped1 refuses a comment on an argument's sign, which prints as `f - -- c` then `x`, read as `f - x`" :=
  refused (App (name "f") [Prefix noisyMinus (name "x")])

test "shaped1 refuses a comment on a head's `-`, which prints as `- -- c` then `1 n`, read as `-(1 n)`" :=
  refused (App (Prefix noisyMinus (number "1")) [name "n"])

test "shaped1 refuses a comment above an argument's operand" :=
  refused
    (App (name "f") [
      sign "-" (Atom Lower (fixedWord "x" { Comments.none | above = [{ text = "-- o", blankBefore = False }] }))
    ])

test "shaped1 accepts the same comment on a sign at the unary level, which the parser builds" :=
  accepted (binary (name "a") "+" (Prefix noisyMinus (name "x")))
