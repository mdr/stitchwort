--| Spacing between two tokens on one line (`crates/fmt/src/spacing.rs`), for
--| the pairs slice 1 meets.
--|
--| Rust decides a gap from the two tokens' kinds and roles, and copies the
--| source's gap where spacing can change meaning. In slice 1 every such
--| pair is decided by the tree instead, since the parser read the gap to
--| build it: an argument minus (`f -2`) is a `Prefix` argument, a
--| subtraction an `Infix`, and `- 2 n` (a `Prefix` of an application of a
--| numeral) a different tree from `-2 n` (an application of `-2`). So the
--| rules write a space between a call's elements, around an infix
--| operator, after `,`, `:` and `:=`, and nothing inside brackets; the one
--| gap with a choice is the one after a prefix operator, here.

namespace Fmt
import Std (Bool, Char, Doc, List, Nat, Option, Text)
import Std.Doc (..)
import Syntax (Expr, Tok, Word, symbol)

--| The gap after a prefix operator: `-x`, `!b`, `¬b`; but `- -x` (not the
--| comment `--x`) and `- 2 n` (SW-3716), which glued would apply `-2`.
def prefixGap (operator: Word) (operand: Expr): Doc :=
  if operator.text == "-" && (operand.firstWord.text == "-" || operand.numeralApplication) then Doc.text " "
  else Nothing

--| An application whose head is a numeral (`numeral_application`).
def Expr.numeralApplication: Expr → Bool
  | App (Atom Num _) _ => True
  | App (Atom Float _) _ => True
  | _ => False

--| The token an operator's spelling is, as the lexer reads it.
def operatorTok (text: Text): Option Tok := match text.toList with
  | [char] =>
    match Tok.unicodeAlias char with
      | Some tok => Some tok
      | None => wholeSymbol text
  | _ => wholeSymbol text

def wholeSymbol (text: Text): Option Tok := match symbol text.toList with
  | Some (tok, length) => if length == text.length then Some tok else None
  | None => None
