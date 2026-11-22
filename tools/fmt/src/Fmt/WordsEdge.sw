--| Which tokens are no closers or comments: a token's spelling decides it (`notCloser`, `notComment`).

namespace Fmt.WordsEdge
import Std (Bool, DecEq, Eq, List, Option, Text)
import Syntax (Comments, Decl, DefBody, Expr, InfixKind, Note, Tok, Word)
import Fmt (..)
import Fmt.SpellProofs (..)
import Fmt.TreeJoinProofs (
  OperatorSpells,
  PrefixSpells,
  QuietKind,
  lexKind,
  lexKindOfSpells,
  operatorSpellsOf,
  spellsNotComment,
  infixListed,
  spellsOfText1,
  wordQuiet
)

-- Tokens that are no closers.

--| A text a token of a kind that is no comma or closer is spelled with is a token that is no closer.
theorem kindPlain ∀ (kind: Tok) (text: Text)
    (spells: Syntax.LexProofs.Spells kind text)
    (quiet: QuietKind kind):
    notCloser text = True ∧ notComment text = True :=
  let kinded: lexKind text = kind := lexKindOfSpells kind text spells
  let (notComma, notParen, notBracket, notBrace) := quiet
  let token: notComment text = True := rewrite spellsNotComment kind text spells
  match a: text == ")" with
    | True => (notParen (rewrite DecEq.sound a at kinded then kinded)).impossible
    | False =>
      match b: text == "]" with
        | True => (notBracket (rewrite DecEq.sound b at kinded then kinded)).impossible
        | False =>
          match c: text == "}" with
            | True => (notBrace (rewrite DecEq.sound c at kinded then kinded)).impossible
            | False =>
              match d: text == "," with
                | True => (notComma (rewrite DecEq.sound d at kinded then kinded)).impossible
                | False => (byComputing, token)

theorem operatorPlain ∀ (text: Text)
    (listed: operatorText1 text = True):
    notCloser text = True ∧ notComment text = True :=
  let (kind, spells, quiet) := operatorSpellsOf text listed
  kindPlain kind text spells quiet

theorem prefixPlain ∀ (text: Text) (listed: prefixText1 text = True): notCloser text = True ∧ notComment text = True :=
  match a: text == "-" with
    | True => rewrite DecEq.sound a then (byComputing, byComputing)
    | False =>
      match b: text == "!" with
        | True => rewrite DecEq.sound b then (byComputing, byComputing)
        | False =>
          match c: text == "¬" with
            | True => rewrite DecEq.sound c then (byComputing, byComputing)

theorem textCloser ∀ (word: Word) (fixed: Text)
    (same: (word.text == fixed) = True)
    (closer: notCloser fixed = False):
    notCloser word.text = False :=
  rewrite DecEq.sound same then closer

-- Closed examples of the token lemmas.

theorem operatorPlainExample: notCloser "+" = True ∧ notComment "+" = True := operatorPlain "+" byComputing

theorem prefixPlainExample: notCloser "!" = True ∧ notComment "!" = True := prefixPlain "!" byComputing

theorem textCloserExample: notCloser (fixedWord ")" Comments.none).text = False :=
  textCloser (fixedWord ")" Comments.none) ")" byComputing byComputing
