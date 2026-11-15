--| The lexer read backwards: on the characters a token is printed as,
--| `lexemeAt` reads exactly them. The start of the lexing layer of the
--| printer's direct proof.

namespace Toy.Syntax.Proofs
import Toy.Syntax (..)
import Std (DecEq, Eq, List, Option, Parse, Text, Void)

--| A character that starts a word is not one that doesn't: for the
--| characters `lexemeStart` tries before a word.
theorem wordStartApart ∀ (first other: Char)
    (starts: isWordStart first = True)
    (apart: isWordStart other = False):
    first ≠ other :=
  same =>
    let both: isWordStart other = True := rewrite <- same in starts
    cases

theorem wordStartIsChar ∀ (first: Char) (starts: isWordStart first = True): isWordChar first = True := cases

--| A text that starts with a letter or `_` starts with a word.
theorem wordLexemeStart ∀ (first: Char) (tail: List Char)
    (starts: isWordStart first = True):
    lexemeStart [first, ..tail] = Some WordLexeme :=
  lexemeStart.eq5 first tail
    (among =>
      match among with
        | Inl same => wordStartApart first ' ' starts rfl (Eq.sym same)
        | Inr (Inl same) => wordStartApart first '\n' starts rfl (Eq.sym same)
        | Inr (Inr (Inl same)) => wordStartApart first '"' starts rfl (Eq.sym same)
        | Inr (Inr (Inr never)) => never)
    (tail1 isMinus sameTail => wordStartApart first '-' starts rfl isMinus)
    starts

--| `lexemeAt` reads a word: a letter or `_`, then letters, digits and `_`s,
--| up to a character that is none of these.
theorem runsWordLexeme ∀ (first: Char) (others rest: List Char)
    (starts: isWordStart first = True)
    (word: others.all isWordChar = True)
    (ends: rest.takeWhile isWordChar = []):
    Parse.Runs (() => lexemeAt ([first, ..others] ++ rest)) [first, ..others] rest WordLexeme :=
  let all: [first, ..others].all isWordChar = True := rewrite wordStartIsChar first starts in word
  rewrite wordLexemeStart first (others ++ rest) starts in
    Parse.runsMap
      (() => Parse.span isWordChar)
      (read => WordLexeme)
      [first, ..others]
      rest
      [first, ..others]
      (Parse.runsSpan isWordChar [first, ..others] rest all ends)
