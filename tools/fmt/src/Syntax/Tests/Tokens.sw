--| The lexer and comment placement on small cases, ported from `crates/fmt`'s
--| `tidy.rs` tests and `crates/syntax`'s lexer tests. The harness
--| (`task fmt:twin STAGE=tokens`) compares whole files with the Rust side;
--| these pin the cases that explain why each rule is there.

namespace Syntax.Tests
import Std (Bool, List, Option, Result, Text)
import Syntax (Leaf, Lexed, Tok, lex)

def kinds (source: Text): List Tok := match lex source with
  | Ok lexed => lexed.leaves.map (leaf => leaf.token.kind)
  | Err _ => []

def refusal (source: Text): Text := match lex source with
  | Ok _ => ""
  | Err message => message

--| A comment placed by comment placement: its text, whether it is on a line of its
--| own, and the text of the token it belongs to (empty at the end).
type Placed = { text: Text, ownLine: Bool, token: Text }

def Leaf.placed (leaf: Leaf): List Placed :=
  let token := leaf.token.text
  let leading := leaf.trivia.leading.map (comment => ({ text = comment.text, ownLine = True, token }: Placed))
  let trailing := leaf.trivia.trailing.map (comment => [({ text = comment.text, ownLine = False, token }: Placed)])
  leading ++ trailing.getOrElse []

def placed (source: Text): List Placed := match lex source with
  | Ok lexed =>
    let settled := lexed.settled
    let ending := settled.end.leading.map (comment => ({ text = comment.text, ownLine = True, token = "" }: Placed))
    settled.leaves.flatMap Leaf.placed ++ ending
  | Err _ => []

def one (source text: Text) (ownLine: Bool) (token: Text): Bool := placed source == [{ text, ownLine, token }]

test "names, keywords and symbols" :=
  kinds "type Type x Xs _ _y x' := : = -> [ ] ( ) , | + 42 - * / % != < <= > >= ! if then else"
    == [KwType, TypeU, Lower, Upper, Underscore, Lower, Lower, ColonEq, Colon, Equals, Arrow, LBracket, RBracket,
      LParen, RParen, Comma, Pipe, Plus, Num, Minus, Star, Slash, Percent, NotEq, Lt, Le, Gt, Ge, Bang, KwIf, KwThen,
      KwElse]

test "numbers, ranges and spreads" :=
  kinds "1.5 1e3 42 0..<n [..xs] xs.0.1 x.exists"
    == [Float, Float, Num, Num, DotDotLt, Lower, LBracket, DotDot, Lower, RBracket, Lower, Dot, Num, Dot, Num, Lower,
      Dot, Lower]

test "an interpolated string's pieces" :=
  kinds "\"a\${x}\${y}b\"" == [StrStart, InterpOpen, Lower, InterpClose, InterpOpen, Lower, InterpClose, StrEnd]

test "lexical refusals" :=
  refusal "def x := \t1" == "tabs aren't allowed; indent with spaces"
    ∧ refusal "def x := \"abc\n" == "this string isn't closed with `\"`"
    ∧ refusal "def x := 'ab'" == "a character literal holds exactly one character"
    ∧ refusal "def x := 1 # 2" == "unexpected character `#`"
    ∧ refusal "def x := \"\"\" a\n\"\"\""
      == "a `\"\"\"` text starts on the next line: nothing may follow the opening `\"\"\"` (use `\"…\"` for one line)"

test "a trailing comment after closers and commas belongs to the code before them" :=
  one "def x := [1, 2] -- c\n" "-- c" False "2"
    ∧ one "def x := [1, 2 -- c\n]\n" "-- c" False "2"
    ∧ one "def x := [\n  1,\n  2\n] -- c\n" "-- c" False "2"
    ∧ one "def x := [f (g y), -- c\n  2]\n" "-- c" False "y"
    ∧ one "def x := { r | -- c\n  a = 1 }\n" "-- c" False "r"
    ∧ one "def x := { (f r) | -- c\n  a = 1 }\n" "-- c" False "r"

test "a trailing comment stays on a closer that would otherwise pass comments" :=
  (placed "def x := [\n  1\n  -- note\n] -- c\n").get 1 == Some { text = "-- c", ownLine = False, token = "]" }
    ∧ (placed "def x := [\n  1 -- a\n] -- b\n").get 1 == Some { text = "-- b", ownLine = False, token = "]" }
    ∧ placed "def a: Nat := (f (1) -- c1\n  ) -- c2\n"
      == [{ text = "-- c1", ownLine = False, token = "1" }, { text = "-- c2", ownLine = False, token = ")" }]

test "a comma's comments go to the token after it" :=
  one "def x := [ 1\n  , 2 -- c\n  ]\n" "-- c" False "2"
    ∧ one "def x := [ 1\n  , -- c\n  2 ]\n" "-- c" True "2"
    ∧ one "def x := [ 1\n  -- c\n  , 2 ]\n" "-- c" True "2"
    ∧ one "def x := [ 1,\n  -- c\n  , ]\n" "-- c" True "]"

test "comments after an arrow, and after an expression let's :=, go before it" :=
  placed "def f: Nat -> -- c\n  -- d\n  Nat := 1\n"
    == [{ text = "-- c", ownLine = True, token = "->" }, { text = "-- d", ownLine = True, token = "->" }]
    ∧ one "def f := (let x := -- c\n  1; x)\n" "-- c" True ":="

test "comment text loses its trailing spaces" :=
  one "def x := 1 -- c  \n" "-- c" False "1" ∧ one "def x := 1\n-- end  \n" "-- end" True ""
