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
    | [] => byComputing
    | [word] => byComputing
    | [word, next, ..rest] =>
      Bool.andIntro (Bool.andLeft bare) (arrowsBarePrefix [next, ..rest] ys (Bool.andRight bare))

theorem startsHeadChar ∀ (mark: Char) (ys zs: List Char)
    (filled: ys.isEmpty = False):
    Text.startsWithChars [mark] (ys ++ zs) = Text.startsWithChars [mark] ys :=
  match ys with | [y, ..more] => byComputing

theorem reverseFilled ∀ (xs acc: List a) (filled: acc.isEmpty = False): (xs.reverseOnto acc).isEmpty = False :=
  match xs with
    | [] => filled
    | [x, ..rest] => reverseFilled rest [x, ..acc] byComputing

theorem allJoin ∀ (xs ys: List a) (p: a → Bool)
    (first: xs.all p = True)
    (second: ys.all p = True):
    (xs ++ ys).all p = True :=
  match xs with
    | [] => second
    | [x, ..rest] => Bool.andIntro (Bool.andLeft first) (allJoin rest ys p (Bool.andRight first) second)

theorem consCong ∀ (x y: a) (xs ys: List a) (head: x = y) (tail: xs = ys): [x, ..xs] = [y, ..ys] := rewrite head, tail

theorem solidSpaces ∀ (text: Text) (solid: isLayout text = False): text.all (char => char == ' ') = False :=
  match spaces: text.all (char => char == ' ') with | False => byComputing

theorem commaNotCloser ∀ (kind: Tok) (comma: (kind == Comma) = True): kind.isCloser = False := cases

theorem wordStartChar ∀ (char: Char) (starts: isWordStart char = True): isWordChar char = True := arithmetic [starts]

theorem andFalseRight ∀ (x: Bool): (x && False) = False := match x with
  | True => byComputing
  | False => byComputing
