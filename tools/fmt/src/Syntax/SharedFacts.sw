--| Small facts that both the `Syntax` and the `Fmt` proofs use (SW-4209): list, character, text and `Tok` lemmas with
--| no formatter-specific content, kept in one place so no proof file restates them. A lemma used by one family only
--| belongs in that family's file; one that two unrelated files need goes here.

namespace Syntax.SharedFacts
import Std (Bool, Char, Eq, List, Text)
import Std.Doc.Proofs (isLayout)
import Syntax (..)
import Fmt (..)

--| Words read newest first stay homed from any point on.
theorem homedBackSuffix ∀ (xs ys: List Word) (homed: homedBack (xs ++ ys) = True): homedBack ys = True := match xs with
  | [] => homed
  | [word, ..rest] => homedBackSuffix rest ys (Bool.andRight homed)

--| `->` bare in a joined list is bare in its second part.
theorem arrowsBareSuffix ∀ (xs ys: List Word) (bare: arrowsBare (xs ++ ys) = True): arrowsBare ys = True :=
  match xs with
    | [] => bare
    | [word] =>
      match ys with
        | [] => byComputing
        | [next, ..more] => Bool.andRight bare
    | [word, next, ..rest] => arrowsBareSuffix [next, ..rest] ys (Bool.andRight bare)

--| `->` bare in a joined list is bare in its first part: the part's last word has nothing after it to read.
theorem arrowsBarePrefix ∀ (xs ys: List Word) (bare: arrowsBare (xs ++ ys) = True): arrowsBare xs = True :=
  match xs with
    | [] | [_] => byComputing
    | [word, next, ..rest] =>
      Bool.andIntro (Bool.andLeft bare) (arrowsBarePrefix [next, ..rest] ys (Bool.andRight bare))

theorem solidSpaces ∀ (text: Text) (solid: isLayout text = False): text.all (char => char == ' ') = False :=
  match spaces: text.all (char => char == ' ') with | False => byComputing

theorem commaNotCloser ∀ (kind: Tok) (comma: (kind == Comma) = True): kind.isCloser = False := cases

theorem wordStartChar ∀ (char: Char) (starts: isWordStart char = True): isWordChar char = True := arithmetic [starts]

theorem headerResultWithin ∀ (header: Header) (within: header.within1 = True): header.result.within1 = True :=
  match header with
    | {
        exportKeyword = None,
        opaqueKeyword = None,
        kind = DefPlain,
        keyword,
        name,
        forallKeyword = None,
        params = [],
        colon,
        result,
        decreasingClause = None,
        unfoldingClause = None
      } => Bool.andRight within
