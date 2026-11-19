--| From `stands1` and `oneLine1` to closers with no comments and blank-line flags only below comments (SW-4110).

namespace Fmt.StandsLine
import Std (Bool, DecEq, Eq, List, Nat, Option, Text)
import Syntax (Comments, Decl, DefBody, Expr, Header, InfixKind, Leaf, Note, Tok, Token, Word)
import Syntax.SettleProofs (tokens)
import Fmt (..)
import Fmt.TreeJoinProofs (lexKind)
import Fmt.OutputStatements (..)
import Fmt.TriviaStatements (..)
import Fmt.LedProofs (..)
import Fmt.Driver1 (..)
import Fmt.OneLineParts (..)

-- Loud words start their lines.

--| A word the rules start a line for: one with own-line comments or a blank line above it, or a closer with a comment
--| after it.
def Word.loud1 (word: Word): Bool :=
  word.noted || word.comments.blankBefore || (word.trails && (lexKind word.text).isCloser)

--| Each word against a token of its text that starts its line if the word is loud, the lists alike in length.
def Loud: List Word → List Token → Bool
  | [], [] => True
  | [word, ..words], [token, ..tokens] =>
    (token.text == word.text) && (!word.loud1 || token.lineStart) && Loud words tokens
  | _, _ => False

def Token.nonComma (token: Token): Bool := !(token.kind == Comma)

theorem loudLeaf ∀ (leaf: Leaf) (word: Word)
    (headed: leaf.headedAs word = True)
    (led: leaf.led = True)
    (kinded: leaf.kinded = True)
    (closer: leaf.kind.isCloser = True → word.comments.after.isSome = True → leaf.token.lineStart = True):
    (!word.loud1 || leaf.token.lineStart) = True :=
  match leaf, word with
    | { token = { kind, text, column, lineStart }, trivia = { leading, blankLines, trailing } }, {
        text = wordText,
        comments = { above, after, blankBefore }
      } =>
      match lineStart, leading, blankLines, above, blankBefore, after, led, headed, closer with
        | True, _, _, _, _, _, _, _, _ => Bool.orRight byComputing
        | False, [_, .._], _, _, _, _, never, _, _ => cases
        | False, [], Succ _, _, _, _, never, _, _ => cases
        | False, [], Zero, [_, .._], _, _, _, never, _ => cases
        | False, [], Zero, [], True, _, _, never, _ => cases
        | False, [], Zero, [], False, None, _, _, _ => byComputing
        | False, [], Zero, [], False, Some _, _, headed, closer =>
          let sameText: text = wordText := DecEq.sound (Bool.andLeft headed)
          let sameKind: kind = lexKind text := DecEq.sound kinded
          match shut: kind.isCloser with
            | True => (Bool.falseNotTrue (closer shut byComputing)).impossible
            | False => rewrite <- sameText, <- sameKind, shut

theorem commaStep ∀ (owed: Option Text) (words: List Word) (leaf: Leaf) (rest: List Leaf)
    (comma: (leaf.kind == Comma) = True)
    (stood: stands owed words [leaf, ..rest] = True):
    ∃ (still: Option Text) => stands still words rest = True :=
  match leaf.kind == Comma, comma, stood with
    | True, _, stood =>
      match tucked owed leaf, stood with
        | Some still, stood => (still, Bool.andRight (Bool.andRight stood))
        | None, never => cases

theorem wordStep ∀ (owed: Option Text) (word: Word) (later: List Word) (leaf: Leaf) (rest: List Leaf)
    (comma: (leaf.kind == Comma) = False)
    (stood: stands owed [word, ..later] [leaf, ..rest] = True):
    leaf.headedAs word = True
      ∧ (leaf.kind.isCloser = True → word.comments.after.isSome = True → leaf.token.lineStart = True)
      ∧ ∃ (still: Option Text) => stands still later rest = True :=
  match leaf.kind == Comma, comma, stood with
    | False, _, stood =>
      match owed, after: word.comments.after, stood with
        | Some _, Some _, never => cases
        | Some owedText, None, stood =>
          let headed := Bool.andLeft stood
          match tucked (Some owedText) leaf, stood with
            | Some still, stood =>
              (headed, (_ never => (Bool.falseNotTrue never).impossible), (still, Bool.andRight (Bool.andRight stood)))
            | None, never => cases
        | None, None, stood => (
          Bool.andLeft stood,
          (_ never => (Bool.falseNotTrue never).impossible),
          (None, Bool.andRight (Bool.andRight stood))
        )
        | None, Some text, stood =>
          let headed := Bool.andLeft stood
          let opens: (!leaf.kind.isCloser || leaf.token.lineStart) = True := Bool.andLeft (Bool.andRight stood)
          let closer: leaf.kind.isCloser = True → (Some text).isSome = True → leaf.token.lineStart = True := shut _ =>
            rewrite shut at opens then opens
          match leaf.trivia.trailing, stood with
            | None, stood => (headed, closer, (Some text, Bool.andRight (Bool.andRight stood)))
            | Some _, stood => (headed, closer, (None, Bool.andRight (Bool.andRight (Bool.andRight stood))))

--| Leaves that stand against words, less their commas, are the words' tokens, each loud word's starting its line.
theorem standsLoud ∀ (owed: Option Text) (words: List Word) (leaves: List Leaf)
    (stood: stands owed words leaves = True)
    (kinded: leaves.all Leaf.kinded = True)
    (led: leaves.all Leaf.led = True):
    Loud words ((tokens leaves).filter Token.nonComma) = True :=
  match leaves, stood with
    | [], stood =>
      match words, stood with
        | [], _ => byComputing
        | [_, .._], never => cases
    | [leaf, ..rest], stood =>
      match comma: leaf.kind == Comma with
        | True =>
          let (still, tail) := commaStep owed words leaf rest comma stood
          standsLoud still words rest tail (Bool.andRight kinded) (Bool.andRight led)
        | False =>
          match words, stood with
            | [], never => cases
            | [word, ..later], stood =>
              let (headed, closer, still, tail) := wordStep owed word later leaf rest comma stood
              Bool.andIntro
                (Bool.andLeft headed)
                (Bool.andIntro
                  (loudLeaf leaf word headed (Bool.andLeft led) (Bool.andLeft kinded) closer)
                  (standsLoud still later rest tail (Bool.andRight kinded) (Bool.andRight led)))
