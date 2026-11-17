--| The goldens through the parser: each source parses to its tree, the
--| source and the formatted text both format to the formatted text, and so
--| does every disturbed copy of it.

namespace Toy.Fmt.Tests
import Toy.Fmt (..)
import Toy.Syntax (..)
import Std (List, Option, Result, Text)

def Golden.formats (golden: Golden) (text: Text): Option Text := format text golden.width |> .toOption

def Golden.parsesToTree (golden: Golden): Bool := parse golden.source == Ok golden.tree

test "each golden's source parses to its tree" := goldens.all Golden.parsesToTree

test "each golden's source formats to its formatted text" :=
  goldens.all (golden => golden.formats golden.source == Some golden.formatted)

test "each golden's formatted text formats to itself" :=
  goldens.all (golden => golden.formats golden.formatted == Some golden.formatted)

test "each golden survives 50 disturbances" := goldens.all (golden => golden.survivesDisturbance golden.formats)

def trailing: Text := "let x = [1, 2,]\nlet y = f(a,)\nfn g(a, b,) = a\n"

def dumped (source: Text): Text := match parse source with
  | Ok tree => tree.dump
  | Err message => message

test "a trailing comma is read and recorded" :=
  dumped trailing
    == "(let x (body (bare (list (item (number 1)) (item (number 2)) ,))))\n(let y (body (bare (call (var f) (item (var a)) ,))))\n(fn g (a b ,) (body (bare (var a))))\n"

test "format drops trailing commas and writes takes" :=
  format trailing 80 == Formatted "let x = [1, 2]\nlet y = f(a)\nfn g takes (a, b) = a\n"

--| P3 at each kind of place: a pair goes where its content is read as it
--| stands (a callee, an operand, either side of an operator by
--| precedence, an item, a body), nested pairs in one run, and a type's;
--| it stays where precedence needs it, where it holds a comment, and
--| where an `if`'s branch has an own-line comment above it, which outside
--| brackets would start a block (toy-plus-plus.md §3.2).
def spareBrackets: Text := """
  let a = ((x))
  let b = (a + b) * c
  let c = a + (b * c)
  let d = -(-x)
  let e = x - (-y)
  let f = (f)((x))
  let g = (a - b) - c
  let h = a - (b - c)
  let i = (( -- kept
    x))
  let j = [(1), (if a then b else c)]
  let k = (if a then
    -- why
    b else c)
  let m = f((if a then
    -- why
    b else c))
  fn n(v: ((Vec))) = (v).w
  """

test "format drops spare brackets and keeps the rest" := format spareBrackets 80 == Formatted """
  let a = x
  let b = (a + b) * c
  let c = a + b * c
  let d = - -x
  let e = x - -y
  let f = f(x)
  let g = a - b - c
  let h = a - (b - c)
  let i =
    ( -- kept
      x)
  let j = [1, if a then b else c]
  let k =
    (if a then
      -- why
      b
    else c)
  let m =
    f(
      if a then
        -- why
        b
      else c
    )
  fn n takes (v: Vec) = v.w
  """

test "format leaves its output without spare brackets alone" := match format spareBrackets 80 with
  | Formatted text => format text 80 == Formatted text
  | ParseError _ => False

--| P4: neighbouring groups with one type are one group, a run of them is,
--| and a type written in brackets counts once P3 has dropped them. Groups
--| stay apart when their types differ, when the first group is untyped, or
--| when a comment sits on the first group's `:` or type
--| (toy-plus-plus.md §3.2).
def mergeable: Text := """
  fn a(w: Int, h: Int, d: Nat, e: (Nat), f: Nat) = w
  fn b(x: Int, -- note
    y: Int) = x
  fn c(p, q: Int, r: Int) = p
  fn d(a: Int, b: Nat) = a
  fn e(a: Int,
    -- above b
    b: Int) = a
  fn f(a: Int, b: (Int -- why
    )) = a
  """

test "format merges groups with one type and keeps the rest" := format mergeable 80 == Formatted """
  fn a takes (w h: Int, d e f: Nat) = w
  fn b takes (
      x: Int, -- note
      y: Int
  ) = x
  fn c takes (p, q r: Int) = p
  fn d takes (a: Int, b: Nat) = a
  fn e takes (
      a
        -- above b
        b: Int
  ) = a
  fn f takes (
      a b: Int -- why
  ) = a
  """

test "format leaves its merged output alone" := match format mergeable 80 with
  | Formatted text => format text 80 == Formatted text
  | ParseError _ => False
