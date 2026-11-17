--| The expression parser on small cases. The harness
--| (`dev/fmt-twin expr`) compares whole dumps with the Rust side's `dev
--| tree --expression`; these pin the layout rules and the tree's shape.

namespace Syntax.Tests
import Std (Bool, List, Option, Result, Text)
import Syntax (Comments, Expr, Note, Word, lex, parseExpression)

def parsed (source: Text): Result Expr Text := match lex source with
  | Ok lexed => parseExpression lexed.settled.leaves
  | Err message => Err message

def dumped (source: Text): Text := match parsed source with
  | Ok tree => tree.dump 0
  | Err message => "error: ${message}"

test "a line indented further continues the application" := dumped "f a\n  b" == "App\n  f\n  a\n  b\n"

test "a line starting with |> continues the pipeline" := dumped "xs\n  |> sum" == "Pipe\n  xs\n  |>\n  sum\n"

test "then and else may start lines at the if's column" :=
  dumped "if c\nthen a\nelse b" == "If\n  if\n  c\n  then\n  a\n  else\n  b\n"

test "an arm out of line with the first ends the match" :=
  dumped "match x with\n  | A => 1\n   | B => 2" == "error: expected the end of the declaration, but found `|`"

test "a line can't start with a method section" := dumped "f\n  .g" == "error: a line can't start with a method section"

test "a trailing comma is a flag, the other commas implied" :=
  dumped "[1, 2,]" == "List\n  [\n  1\n  ,\n  2\n  ,\n  ]\n"
    && (match parsed "[1, 2,]" with
      | Ok (ListOf _ items trailingComma _) => items.length == 2 && trailingComma
      | _ => False)

test "a word keeps its text and comments, not its layout" := match parsed "f\n\n  -- note\n  x -- after" with
  | Ok (App _ [Atom _ word]) =>
    word == { text = "x", comments = { above = [{ text = "-- note", blankBefore = True }], after = Some "-- after" } }
  | _ => False

--| `fuelEnough` on chains 200 deep: each call of `self` or `pself` follows
--| a read, so the items left and one more is fuel enough (spike K4).
def nested (depth: Nat) (open inner close: Text): Text := "${open.repeat depth}${inner}${close.repeat depth}"

def readsWhole (source: Text): Bool := match parsed source with
  | Ok _ => True
  | Err _ => False

test "brackets, prefixes and lambdas nested 200 deep" :=
  readsWhole (nested 200 "(" "1" ")")
    && readsWhole (nested 200 "- " "1" "")
    && readsWhole (nested 200 "f (" "x" ")")
    && readsWhole (nested 200 "y => " "1" "")
    && readsWhole (nested 200 "match y with | _ => " "1" "")

test "patterns nested 200 deep" :=
  readsWhole "match y with | ${nested 200 "(" "a" ")"} => 1"
    && readsWhole "match y with | ${nested 200 "(A | " "B" ")"} => 1"
    && readsWhole "match y with | ${nested 200 "(-1, " "-2" ")"} => 1"
    && readsWhole "match y with | ${nested 200 "[A | " "B" "]"} => 1"
    && readsWhole "match y with | ${nested 200 "(\"s\" ++ " "r" ")"} => 1"

--| The `.` after a `"""` text is glued to its closing quotes, which are
--| at the end of the text's last line, not a text's length after its start.
test "a field access on a block text" :=
  dumped "f \"\"\"\n  x\n  \"\"\".lines" == "App\n  f\n  FieldAccess\n    \"\"\"\n  x\n  \"\"\"\n    .\n    lines\n"
