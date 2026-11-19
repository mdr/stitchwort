--| From `stands1` and `oneLine1` to closers with no comments and blank-line flags only below comments (SW-4110).

namespace Fmt.StandsLine
import Std (Bool, DecEq, Eq, List, Nat, Option, Text)
import Syntax (Comments, Decl, DefBody, Expr, Header, InfixKind, Leaf, Note, Tok, Token, Word)
import Syntax.SettleProofs (tokens)
import Fmt (..)
import Fmt.TreeJoinProofs (infixListed, lexKind, lexKindOfSpells, spellsOfText1, wordQuiet)
import Fmt.OutputStatements (..)
import Fmt.TriviaStatements (..)
import Fmt.LedProofs (..)
import Fmt.Driver1 (..)
import Fmt.OneLineParts (..)
import Fmt.SpellProofs (..)
import Fmt.TokenProofs (declRealOfLexical, printedTokens1)
import Fmt.WordsEdge (kindPlain)
import Fmt.CalmProofs (headerResultWithin)
import Fmt.WordsEdgeLine (..)

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

--| A word the rules leave where the line goes on.
def Word.still1 (word: Word): Bool := !word.loud1

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

-- Splitting the tokens by the words.

theorem loudSplit ∀ (front back: List Word) (tokens: List Token)
    (loud: Loud (front ++ back) tokens = True):
    ∃ (first second: List Token) => tokens = first ++ second ∧ Loud front first = True ∧ Loud back second = True :=
  match front, tokens, loud with
    | [], tokens, loud => ([], tokens, byComputing, byComputing, loud)
    | [word, ..words], [token, ..others], loud =>
      let (first, second, split, frontLoud, backLoud) :=
        loudSplit words back others (Bool.andRight (Bool.andRight loud))
      (
        [token, ..first],
        second,
        (rewrite split),
        Bool.andIntro (Bool.andLeft loud) (Bool.andIntro (Bool.andLeft (Bool.andRight loud)) frontLoud),
        backLoud
      )

theorem loudQuiet ∀ (words: List Word) (tokens: List Token)
    (loud: Loud words tokens = True)
    (quiet: tokens.all (token => !token.lineStart) = True):
    words.all Word.still1 = True :=
  match words, tokens, loud with
    | [], [], _ => byComputing
    | [word, ..rest], [token, ..others], loud =>
      let starts: token.lineStart = False := Bool.notTrue _ (Bool.andLeft quiet)
      let step: (!word.loud1 || token.lineStart) = True := Bool.andLeft (Bool.andRight loud)
      Bool.andIntro
        (rewrite starts at step then rewrite Bool.orFalse (!word.loud1) at step then step)
        (loudQuiet rest others (Bool.andRight (Bool.andRight loud)) (Bool.andRight quiet))

--| A word the lexer reads as no `:=`.
def Word.notAssign1 (word: Word): Bool := notAssign word.text

--| A token that is no `:=`.
def Token.notAssign1 (token: Token): Bool := !(token.kind == ColonEq)

theorem loudAssign ∀ (words: List Word) (tokens: List Token)
    (loud: Loud words tokens = True)
    (kinded: tokens.all Token.kinded1 = True)
    (other: words.all Word.notAssign1 = True):
    tokens.all Token.notAssign1 = True :=
  match words, tokens, loud with
    | [], [], _ => byComputing
    | [word, ..rest], [token, ..others], loud =>
      let sameText: token.text = word.text := DecEq.sound (Bool.andLeft loud)
      let sameKind: token.kind = lexKind token.text := DecEq.sound (Bool.andLeft kinded)
      let head: Token.notAssign1 token = True := rewrite sameKind, sameText then Bool.andLeft other
      Bool.andIntro head
        (loudAssign rest others (Bool.andRight (Bool.andRight loud)) (Bool.andRight kinded) (Bool.andRight other))

-- `onLine1` with the commas left out.

theorem allFilter ∀ (tokens: List Token) (keep check: Token → Bool)
    (all: tokens.all check = True):
    (tokens.filter keep).all check = True :=
  match tokens with
    | [] => byComputing
    | [token, ..rest] =>
      match keep token with
        | True => Bool.andIntro (Bool.andLeft all) (allFilter rest keep check (Bool.andRight all))
        | False => allFilter rest keep check (Bool.andRight all)

theorem valueQuietAll ∀ (tokens: List Token)
    (quiet: tokens.all (token => !token.lineStart) = True):
    valueOnLine1 tokens = True :=
  match tokens with
    | [] => byComputing
    | [token, ..rest] => Bool.andRight quiet

theorem valueFilter ∀ (tokens: List Token)
    (line: valueOnLine1 tokens = True):
    valueOnLine1 (tokens.filter Token.nonComma) = True :=
  match tokens, line with
    | [], _ => byComputing
    | [token, ..rest], line =>
      match token.nonComma with
        | True => allFilter rest Token.nonComma (token => !token.lineStart) line
        | False =>
          valueQuietAll (rest.filter Token.nonComma) (allFilter rest Token.nonComma (token => !token.lineStart) line)

theorem typeFilter ∀ (tokens: List Token)
    (line: typeOnLine1 tokens = True):
    typeOnLine1 (tokens.filter Token.nonComma) = True :=
  match tokens, line with
    | [], _ => byComputing
    | [token, ..rest], line =>
      match colon: token.kind == ColonEq, line with
        | True, line =>
          let kept: token.nonComma = True := rewrite DecEq.sound colon
          rewrite kept, colon then valueFilter rest line
        | False, line =>
          match token.nonComma with
            | True => rewrite colon then Bool.andIntro (Bool.andLeft line) (typeFilter rest (Bool.andRight line))
            | False => typeFilter rest (Bool.andRight line)

theorem typeSplitTokens ∀ (front back: List Token)
    (other: front.all Token.notAssign1 = True)
    (line: typeOnLine1 (front ++ back) = True):
    front.all (token => !token.lineStart) = True ∧ typeOnLine1 back = True :=
  match front with
    | [] => (byComputing, line)
    | [token, ..rest] =>
      let notColon: (token.kind == ColonEq) = False := Bool.notTrue _ (Bool.andLeft other)
      let stepped: (!token.lineStart && typeOnLine1 (rest ++ back)) = True := rewrite notColon at line then line
      let (quiet, after) := typeSplitTokens rest back (Bool.andRight other) (Bool.andRight stepped)
      (Bool.andIntro (Bool.andLeft stepped) quiet, after)

-- From the words to the tree.

--| Every word after the first is still.
def tailStill: List Word → Bool
  | [] => True
  | [_, ..rest] => rest.all Word.still1

theorem tailOfAll ∀ (words: List Word) (all: words.all Word.still1 = True): tailStill words = True := match words with
  | [] => byComputing
  | [word, ..rest] => Bool.andRight all

theorem tailSplit ∀ (front back: List Word)
    (still: tailStill (front ++ back) = True):
    tailStill front = True ∧ tailStill back = True :=
  match front with
    | [] => (byComputing, still)
    | [word, ..rest] =>
      let (restStill, backStill) := allSplitBool rest back Word.still1 still
      (restStill, tailOfAll back backStill)

theorem closeBare ∀ (word: Word)
    (closer: (lexKind word.text).isCloser = True)
    (still: word.still1 = True):
    word.bare1 = True :=
  match word with
    | { text, comments = { above, after, blankBefore } } =>
      let quiet: (!(!above.isEmpty || blankBefore || (after.isSome && (lexKind text).isCloser))) = True := still
      let shut: (!(!above.isEmpty || blankBefore || after.isSome)) = True :=
        rewrite closer, Bool.andTrue after.isSome at quiet then quiet
      match above, blankBefore, after, shut with
        | [], False, None, _ => byComputing

theorem closeOf ∀ (word: Word) (closer: Text)
    (text: (word.text == closer) = True)
    (kind: (lexKind closer).isCloser = True)
    (still: word.still1 = True):
    word.bare1 = True :=
  closeBare word (rewrite DecEq.sound text then kind) still

--| The closers of an expression whose words after the first are still have no comments, after `calm`.
--|
--| Proof idea: by induction on the expression; a closer is never an expression's first word, so each is still, and
--| a still closer is bare (`closeBare`).
theorem closersOfTail ∀ (expr: Expr) (item: Bool)
    (within: expr.within1 = True)
    (lexical: expr.lexical1 = True)
    (still: tailStill (expr.calm item).words = True):
    (expr.calm item).closersBare1 = True :=
  match expr with
    | Atom _ _ => byComputing
    | Paren open inner close =>
      let (_, closeText, innerLexical) := lexical
      let (innerStill, closeStill) := allSplitBool (inner.calm False).words [close.kept False True] Word.still1 still
      Bool.andIntro
        (closersOfTail inner False within innerLexical (tailOfAll _ innerStill))
        (closeOf (close.kept False True) ")" closeText byComputing (Bool.andLeft closeStill))
    | Tuple open items _ close =>
      let (_, closeText, itemsLexical) := lexical
      let (itemsStill, closeStill) :=
        allSplitBool (itemsWords (calmAll True items)) [close.kept False True] Word.still1 still
      Bool.andIntro
        (itemsClosers items True within itemsLexical (tailOfAll _ itemsStill))
        (closeOf (close.kept False True) ")" closeText byComputing (Bool.andLeft closeStill))
    | ListOf open items _ close =>
      let (_, closeText, itemsLexical) := lexical
      let (itemsStill, closeStill) :=
        allSplitBool (itemsWords (calmItems items)) [close.kept False True] Word.still1 still
      Bool.andIntro
        (pickClosers items within itemsLexical (tailOfAll _ itemsStill))
        (closeOf (close.kept False True) "]" closeText byComputing (Bool.andLeft closeStill))
    | App head arguments =>
      let (headStill, argumentsStill) := tailSplit (head.calm item).words (itemsWords (calmAll False arguments)) still
      Bool.andIntro
        (closersOfTail head item (Bool.andLeft within) (Bool.andLeft lexical) headStill)
        (itemsClosers arguments False (Bool.andRight within) (Bool.andRight lexical) argumentsStill)
    | Infix kind left operator right =>
      let (leftStill, restStill) :=
        tailSplit (left.calm item).words [operator.kept False False, ..(right.calm False).words] still
      let (leftLexical, _, rightLexical) := lexical
      match kind with
        | InfixBinary =>
          let (leftWithin, rightWithin, _) := within
          Bool.andIntro
            (closersOfTail left item leftWithin leftLexical leftStill)
            (closersOfTail right False rightWithin rightLexical (tailOfAll _ restStill))
        | InfixArrow =>
          let (leftWithin, rightWithin, _) := within
          Bool.andIntro
            (closersOfTail left item leftWithin leftLexical leftStill)
            (closersOfTail right False rightWithin rightLexical (tailOfAll _ restStill))
        | _ => cases
    | Prefix operator operand =>
      closersOfTail operand False (Bool.andLeft within) (Bool.andRight lexical) (tailOfAll _ still)

theorem itemsClosers ∀ (items: List Expr) (item: Bool)
    (within: allWithin1 items = True)
    (lexical: allLexical1 items = True)
    (still: tailStill (itemsWords (calmAll item items)) = True):
    allClosersBare1 (calmAll item items) = True :=
  match items with
    | [] => byComputing
    | [first, ..rest] =>
      let (firstStill, restStill) := tailSplit (first.calm item).words (itemsWords (calmAll item rest)) still
      Bool.andIntro
        (closersOfTail first item (Bool.andLeft within) (Bool.andLeft lexical) firstStill)
        (itemsClosers rest item (Bool.andRight within) (Bool.andRight lexical) restStill)

theorem pickClosers ∀ (items: List Expr)
    (within: allWithin1 items = True)
    (lexical: allLexical1 items = True)
    (still: tailStill (itemsWords (calmItems items)) = True):
    allClosersBare1 (calmItems items) = True :=
  match plain: items.all Expr.plainItem, still with
    | False, still => itemsClosers items True within lexical still
    | True, still =>
      match items, still with
        | [], _ => byComputing
        | [first, ..rest], still =>
          let (firstStill, restStill) := tailSplit (first.calm False).words (itemsWords (calmAll True rest)) still
          Bool.andIntro
            (closersOfTail first False (Bool.andLeft within) (Bool.andLeft lexical) firstStill)
            (itemsClosers rest True (Bool.andRight within) (Bool.andRight lexical) restStill)

-- Blank-line flags.

--| The first word's blank-line flag, if set, is below own-line comments.
def headBelow: List Word → Bool
  | [] => True
  | [word, .._] => word.blankBelow1

theorem headAppend ∀ (front back: List Word)
    (frontBelow: headBelow front = True)
    (backBelow: headBelow back = True):
    headBelow (front ++ back) = True :=
  match front with
    | [] => backBelow
    | [word, ..rest] => frontBelow

theorem keptBelow ∀ (word: Word) (closer: Bool): (word.kept False closer).blankBelow1 = True := match word with
  | { text, comments = { above, after, blankBefore } } =>
    match above, blankBefore with
      | [], True => byComputing
      | [], False => byComputing
      | [_, .._], _ => byComputing

--| `calm` with no item clears the first word's blank-line flag unless comments are above it.
theorem calmHead ∀ (expr: Expr) (within: expr.within1 = True): headBelow (expr.calm False).words = True :=
  match expr with
    | Atom _ word => keptBelow word False
    | Paren open _ _ => keptBelow open False
    | Tuple open _ _ _ => keptBelow open False
    | ListOf open _ _ _ => keptBelow open False
    | App head arguments =>
      headAppend
        (head.calm False).words
        (itemsWords (calmAll False arguments))
        (calmHead head (Bool.andLeft within))
        (itemsHead arguments (Bool.andRight within))
    | Infix kind left operator right =>
      match kind with
        | InfixBinary =>
          headAppend
            (left.calm False).words
            [operator.kept False False, ..(right.calm False).words]
            (calmHead left (Bool.andLeft within))
            (keptBelow operator False)
        | InfixArrow =>
          headAppend
            (left.calm False).words
            [operator.kept False False, ..(right.calm False).words]
            (calmHead left (Bool.andLeft within))
            (keptBelow operator False)
        | _ => cases
    | Prefix operator _ => keptBelow operator False

theorem itemsHead ∀ (items: List Expr)
    (within: allWithin1 items = True):
    headBelow (itemsWords (calmAll False items)) = True :=
  match items with
    | [] => byComputing
    | [first, ..rest] =>
      headAppend
        (first.calm False).words
        (itemsWords (calmAll False rest))
        (calmHead first (Bool.andLeft within))
        (itemsHead rest (Bool.andRight within))

theorem stillBelow ∀ (word: Word) (still: word.still1 = True): word.blankBelow1 = True := match word with
  | { text, comments = { above, after, blankBefore } } =>
    match above, blankBefore, still with
      | [], False, _ => byComputing
      | [], True, never => cases
      | [_, .._], _, _ => byComputing

theorem allBelow ∀ (words: List Word) (all: words.all Word.still1 = True): words.all Word.blankBelow1 = True :=
  match words with
    | [] => byComputing
    | [word, ..rest] => Bool.andIntro (stillBelow word (Bool.andLeft all)) (allBelow rest (Bool.andRight all))

theorem headTailBelow ∀ (words: List Word)
    (head: headBelow words = True)
    (still: tailStill words = True):
    words.all Word.blankBelow1 = True :=
  match words with
    | [] => byComputing
    | [word, ..rest] => Bool.andIntro head (allBelow rest still)

-- No word of the type is a `:=`.

theorem fixedNotAssign ∀ (word: Word) (fixed: Text)
    (same: (word.text == fixed) = True)
    (other: notAssign fixed = True):
    word.notAssign1 = True :=
  rewrite DecEq.sound same then other

theorem calmAssign ∀ (expr: Expr) (item: Bool)
    (within: expr.within1 = True)
    (lexical: expr.lexical1 = True):
    (expr.calm item).words.all Word.notAssign1 = True :=
  match expr with
    | Atom kind word => Bool.andIntro (atomAssign kind word within) byComputing
    | Paren open inner close =>
      let (openText, closeText, innerLexical) := lexical
      Bool.andIntro
        (fixedNotAssign (open.kept item False) "(" openText byComputing)
        (rewrite allAppendBool (inner.calm False).words [close.kept False True] Word.notAssign1 then
          Bool.andIntro
            (calmAssign inner False within innerLexical)
            (Bool.andIntro (fixedNotAssign (close.kept False True) ")" closeText byComputing) byComputing))
    | Tuple open items _ close =>
      let (openText, closeText, itemsLexical) := lexical
      Bool.andIntro
        (fixedNotAssign (open.kept item False) "(" openText byComputing)
        (rewrite allAppendBool (itemsWords (calmAll True items)) [close.kept False True] Word.notAssign1 then
          Bool.andIntro
            (itemsAssign items True within itemsLexical)
            (Bool.andIntro (fixedNotAssign (close.kept False True) ")" closeText byComputing) byComputing))
    | ListOf open items _ close =>
      let (openText, closeText, itemsLexical) := lexical
      Bool.andIntro
        (fixedNotAssign (open.kept item False) "[" openText byComputing)
        (rewrite allAppendBool (itemsWords (calmItems items)) [close.kept False True] Word.notAssign1 then
          Bool.andIntro
            (pickAssign items within itemsLexical)
            (Bool.andIntro (fixedNotAssign (close.kept False True) "]" closeText byComputing) byComputing))
    | App head arguments =>
      rewrite allAppendBool (head.calm item).words (itemsWords (calmAll False arguments)) Word.notAssign1 then
        Bool.andIntro
          (calmAssign head item (Bool.andLeft within) (Bool.andLeft lexical))
          (itemsAssign arguments False (Bool.andRight within) (Bool.andRight lexical))
    | Infix kind left operator right =>
      let (leftLexical, _, rightLexical) := lexical
      let listed := infixListed kind left operator right within
      rewrite allAppendBool
            (left.calm item).words
            [operator.kept False False, ..(right.calm False).words]
            Word.notAssign1 then
        match kind with
          | InfixBinary =>
            let (leftWithin, rightWithin, _) := within
            Bool.andIntro
              (calmAssign left item leftWithin leftLexical)
              (Bool.andIntro (operatorAssign operator.text listed) (calmAssign right False rightWithin rightLexical))
          | InfixArrow =>
            let (leftWithin, rightWithin, _) := within
            Bool.andIntro
              (calmAssign left item leftWithin leftLexical)
              (Bool.andIntro (operatorAssign operator.text listed) (calmAssign right False rightWithin rightLexical))
          | _ => cases
    | Prefix operator operand =>
      let (operandWithin, prefixed) := within
      Bool.andIntro
        (prefixAssign operator.text prefixed)
        (calmAssign operand False operandWithin (Bool.andRight lexical))

theorem itemsAssign ∀ (items: List Expr) (item: Bool)
    (within: allWithin1 items = True)
    (lexical: allLexical1 items = True):
    (itemsWords (calmAll item items)).all Word.notAssign1 = True :=
  match items with
    | [] => byComputing
    | [first, ..rest] =>
      rewrite allAppendBool (first.calm item).words (itemsWords (calmAll item rest)) Word.notAssign1 then
        Bool.andIntro
          (calmAssign first item (Bool.andLeft within) (Bool.andLeft lexical))
          (itemsAssign rest item (Bool.andRight within) (Bool.andRight lexical))

theorem pickAssign ∀ (items: List Expr)
    (within: allWithin1 items = True)
    (lexical: allLexical1 items = True):
    (itemsWords (calmItems items)).all Word.notAssign1 = True :=
  match plain: items.all Expr.plainItem with
    | False => itemsAssign items True within lexical
    | True =>
      match items with
        | [] => byComputing
        | [first, ..rest] =>
          rewrite allAppendBool (first.calm False).words (itemsWords (calmAll True rest)) Word.notAssign1 then
            Bool.andIntro
              (calmAssign first False (Bool.andLeft within) (Bool.andLeft lexical))
              (itemsAssign rest True (Bool.andRight within) (Bool.andRight lexical))

-- The declaration.

theorem tokensSplit ∀ (front back: List Token) (check: Token → Bool)
    (all: (front ++ back).all check = True):
    front.all check = True ∧ back.all check = True :=
  match front with
    | [] => (byComputing, all)
    | [token, ..rest] =>
      let (restAll, backAll) := tokensSplit rest back check (Bool.andRight all)
      (Bool.andIntro (Bool.andLeft all) restAll, backAll)

theorem loudTail ∀ (words: List Word) (tokens: List Token)
    (loud: Loud words tokens = True)
    (line: valueOnLine1 tokens = True):
    tailStill words = True :=
  match words, tokens, loud with
    | [], [], _ => byComputing
    | [word, ..rest], [token, ..others], loud => loudQuiet rest others (Bool.andRight (Bool.andRight loud)) line

theorem stoodShape ∀ (header: Header) (colonEq: Syntax.Comments) (value: Expr):
    ∃ (first second third: Word) => (Definition [] header (Assigned colonEq value)).stood
      = [first, second, third]
        ++ ((header.result.calm False).words
          ++ ([fixedWord ":=" (colonEq.kept False False)] ++ (value.calm False).words)) :=
  (
    { text = "def", comments = { above = [], after = header.keyword.after, blankBefore = False } },
    header.name.kept False False,
    fixedWord ":" (header.colon.kept False False),
    byComputing
  )

--| A slice 1 definition's tokens begin with `def`, its name and `:`.
theorem headTexts ∀ (header: Header) (colonEq: Syntax.Comments) (value: Expr)
    (within: (Definition [] header (Assigned colonEq value)).within1 = True)
    (settled: (Definition [] header (Assigned colonEq value)).settled1 = True)
    (lexical: (Definition [] header (Assigned colonEq value)).lexical1 = True):
    ∃ (more: List Text) => (Definition [] header (Assigned colonEq value)).spelt.filter notComment
      = ["def", header.name.text, ":"] ++ more :=
  let (headerWithin, _) := within
  let nameWithin := headerNameWithin header headerWithin
  let (_, nameToken) :=
    kindPlain Lower header.name.text
      (spellsOfText1 Lower header.name.text (Bool.andRight nameWithin))
      (wordQuiet Lower byComputing)
  let sound := declSoundOfSettled _ within settled (declRealOfLexical _ within lexical)
  let (defSound, nameSound, colonSound, _, _, _) := sound
  let head :=
    ((fixedWord "def" header.keyword).spelledAt True ++ header.name.spelledAt False)
      ++ (fixedWord ":" header.colon).spelledAt False
  let later := header.result.spelt False ++ ((fixedWord ":=" colonEq).spelledAt False ++ value.spelt False)
  let headTokens: head.filter notComment = ["def", header.name.text, ":"] :=
    rewrite List.filterAppend
          ((fixedWord "def" header.keyword).spelledAt True ++ header.name.spelledAt False)
          ((fixedWord ":" header.colon).spelledAt False)
          notComment,
        List.filterAppend ((fixedWord "def" header.keyword).spelledAt True) (header.name.spelledAt False) notComment,
        wordTokens (fixedWord "def" header.keyword) True byComputing defSound,
        wordTokens header.name False nameToken nameSound,
        wordTokens (fixedWord ":" header.colon) False byComputing colonSound
  (
    later.filter notComment,
    calc (Definition [] header (Assigned colonEq value)).spelt.filter notComment
      _ = (head ++ later).filter notComment :=
        Eq.cong ((spelt: List Text) => spelt.filter notComment) (speltParts header colonEq value)
      _ = head.filter notComment ++ later.filter notComment := List.filterAppend head later notComment
      _ = ["def", header.name.text, ":"] ++ later.filter notComment := rewrite headTokens
  )

theorem keepOf ∀ (token: Token) (text: Text)
    (same: token.text = text)
    (kinded: token.kinded1 = True)
    (kind: (lexKind text == Comma) = False):
    token.nonComma = True :=
  let kindEq: token.kind = lexKind text := rewrite <- same then DecEq.sound kinded
  rewrite kindEq, kind

--| Printed tokens that begin with `def`, a name and `:`, laid out as `onLine1` says, keep those three with the commas
--| left out, and the type's tokens and the value's follow as `typeOnLine1` says.
theorem headKept ∀ (tokens: List Token) (name: Text) (more: List Text)
    (texts: tokens.map (token => token.text) = ["def", name, ":"] ++ more)
    (kinded: tokens.all Token.kinded1 = True)
    (nameKind: lexKind name = Lower)
    (line: onLine1 tokens = True):
    ∃ (first second third: Token) (rest: List Token) => tokens.filter Token.nonComma
      = [first, second, third, ..rest.filter Token.nonComma]
      ∧ typeOnLine1 rest = True
      ∧ rest.all Token.kinded1 = True :=
  match tokens, line with
    | [a, b, c, ..rest], line =>
      let aText: a.text = "def" := List.consInjectiveHead _ _ _ _ texts
      let bText: b.text = name := List.consInjectiveHead _ _ _ _ (Eq.cong ((list: List Text) => list.drop 1) texts)
      let cText: c.text = ":" := List.consInjectiveHead _ _ _ _ (Eq.cong ((list: List Text) => list.drop 2) texts)
      let aKeep := keepOf a "def" aText (Bool.andLeft kinded) byComputing
      let bKeep := keepOf b name bText (Bool.andLeft (Bool.andRight kinded)) (rewrite nameKind)
      let cKeep := keepOf c ":" cText (Bool.andLeft (Bool.andRight (Bool.andRight kinded))) byComputing
      (a, b, c, rest, (rewrite aKeep, bKeep, cKeep), line, Bool.andRight (Bool.andRight (Bool.andRight kinded)))

--| The type's words are still, and the value's after the first.
def Decl.stillParts1: Decl → Bool
  | Definition [] header (Assigned _ value) =>
    (header.result.calm False).words.all Word.still1 && tailStill (value.calm False).words
  | _ => False

--| Tokens of a slice 1 definition's spelling, laid out as `onLine1` says, against which the definition's words are
--| `Loud`, leave the type's words still, and the value's after the first.
--|
--| Proof idea: the tokens begin with `def`, the name and `:`, none a comma (`headKept`); then come the type's, none a
--| `:=` (`calmAssign`), which start no line, then the `:=`, then the value's, which start none after the first.
theorem stillOfTokens ∀ (decl: Decl) (printed: List Token)
    (within: decl.within1 = True)
    (settled: decl.settled1 = True)
    (lexical: decl.lexical1 = True)
    (loud: Loud decl.stood (printed.filter Token.nonComma) = True)
    (texts: printed.map (token => token.text) = decl.spelt.filter notComment)
    (kinded: printed.all Token.kinded1 = True)
    (line: onLine1 printed = True):
    decl.stillParts1 = True :=
  match decl with
    | Definition [] header (Assigned colonEq value) =>
      let (headerWithin, _) := within
      let resultWithin := headerResultWithin header headerWithin
      let nameWithin := headerNameWithin header headerWithin
      let (_, resultLexical, _) := lexical
      let (more, headIs) := headTexts header colonEq value within settled lexical
      let nameKind: lexKind header.name.text = Lower :=
        lexKindOfSpells Lower header.name.text (spellsOfText1 Lower header.name.text (Bool.andRight nameWithin))
      let (a, b, c, rest, kept, typeLine, restKinded) :=
        headKept printed header.name.text more (Eq.trans texts headIs) kinded nameKind line
      let (h1, h2, h3, stoodIs) := stoodShape header colonEq value
      let typeWords := (header.result.calm False).words
      let assign := fixedWord ":=" (colonEq.kept False False)
      let valueWords := (value.calm False).words
      let split: Loud ([h1, h2, h3] ++ (typeWords ++ ([assign] ++ valueWords))) [a, b, c, ..rest.filter Token.nonComma]
        = True :=
        rewrite <- stoodIs, <- kept then loud
      let restLoud: Loud (typeWords ++ ([assign] ++ valueWords)) (rest.filter Token.nonComma) = True :=
        Bool.andRight (Bool.andRight (Bool.andRight (Bool.andRight (Bool.andRight (Bool.andRight split)))))
      let (typeTokens, later, tokensIs, typeLoud, laterLoud) :=
        loudSplit typeWords ([assign] ++ valueWords) (rest.filter Token.nonComma) restLoud
      let filteredLine: typeOnLine1 (typeTokens ++ later) = True := rewrite <- tokensIs then typeFilter rest typeLine
      let filteredKinded: (typeTokens ++ later).all Token.kinded1 = True :=
        rewrite <- tokensIs then allFilter rest Token.nonComma Token.kinded1 restKinded
      let (typeKinded, laterKinded) := tokensSplit typeTokens later Token.kinded1 filteredKinded
      let typeOther :=
        loudAssign typeWords typeTokens typeLoud typeKinded (calmAssign header.result False resultWithin resultLexical)
      let (typeQuiet, laterLine) := typeSplitTokens typeTokens later typeOther filteredLine
      match later, laterLoud, laterLine, laterKinded with
        | [assignToken, ..valueTokens], laterLoud, laterLine, laterKinded =>
          let assignText: assignToken.text = ":=" := DecEq.sound (Bool.andLeft laterLoud)
          let assignKind: (assignToken.kind == ColonEq) = True :=
            rewrite DecEq.sound (Bool.andLeft laterKinded), assignText
          let valueLine: valueOnLine1 valueTokens = True := rewrite assignKind at laterLine then laterLine
          Bool.andIntro
            (loudQuiet typeWords typeTokens typeLoud typeQuiet)
            (loudTail valueWords valueTokens (Bool.andRight (Bool.andRight laterLoud)) valueLine)

--| A slice 1 definition that `stands1` and prints on one line has its type's words still, and its value's after the
--| first.
theorem stillOfStands ∀ (decl: Decl)
    (within: decl.within1 = True)
    (shaped: decl.shaped1 = True)
    (settled: decl.settled1 = True)
    (lexical: decl.lexical1 = True)
    (stood: decl.stands1 = True)
    (oneLine: decl.oneLine1 = True):
    decl.stillParts1 = True :=
  let (texts, kinded) := printedTokens1 decl within shaped settled lexical
  stillOfTokens decl
    (tokens decl.leaves1)
    within
    settled
    lexical
    (standsLoud None decl.stood decl.leaves1 stood kinded (leavesLed decl))
    (Eq.trans (textsTokens decl.leaves1) texts)
    (kindedTokens decl.leaves1 kinded)
    oneLine

-- The parts.

--| A declaration that `stands1` and prints on one line has bare closers (`Fmt.OneLineLays.closersBareOfStands`).
theorem closersBareStands ∀ (decl: Decl)
    (within: decl.within1 = True)
    (shaped: decl.shaped1 = True)
    (settled: decl.settled1 = True)
    (lexical: decl.lexical1 = True)
    (stood: decl.stands1 = True)
    (oneLine: decl.oneLine1 = True):
    decl.closersBare1 = True :=
  let parts := stillOfStands decl within shaped settled lexical stood oneLine
  match decl, within, lexical, parts with
    | Definition [] header (Assigned colonEq value), within, lexical, parts =>
      let (headerWithin, valueWithin) := within
      let (_, resultLexical, valueLexical) := lexical
      Bool.andIntro
        (closersOfTail header.result False
          (headerResultWithin header headerWithin)
          resultLexical
          (tailOfAll _ (Bool.andLeft parts)))
        (closersOfTail value False valueWithin valueLexical (Bool.andRight parts))

--| A declaration that `stands1` and prints on one line has blank-line flags only below own-line comments
--| (`Fmt.OneLineLays.blanksBelowOfStands`).
theorem blanksBelowStands ∀ (decl: Decl)
    (within: decl.within1 = True)
    (shaped: decl.shaped1 = True)
    (settled: decl.settled1 = True)
    (lexical: decl.lexical1 = True)
    (stood: decl.stands1 = True)
    (oneLine: decl.oneLine1 = True):
    decl.blanksBelow1 = True :=
  let parts := stillOfStands decl within shaped settled lexical stood oneLine
  match decl, within, parts with
    | Definition [] header (Assigned colonEq value), within, parts =>
      let (_, valueWithin) := within
      Bool.andIntro
        (allBelow (header.result.calm False).words (Bool.andLeft parts))
        (headTailBelow (value.calm False).words (calmHead value valueWithin) (Bool.andRight parts))

-- Sources the statements apply to (D3684).

--| Whether every declaration of a source's printed tree has its type's words still, and its value's after the first.
def stillPartsOn (source: Text): Option Bool := match tidiedOf source with
  | None => None
  | Some file => Some (file.decls.all Decl.stillParts1)

--| `stillOfStands` applies to the source of `Fmt.OneLineLays.standsLineHolds`: comments after a name, at `:=` and
--| above the value, and a comment held after the value's last item. A closer below a comment that holds another is
--| loud, and that declaration prints on two lines (`standsLineApart`).
theorem stillPartsExamples: (stillPartsOn "def x: F a -- c\n  := -- d\n  -- e\n  -- f\n\n  g (b, c -- h\n  )\n"
      == Some True
      && stillPartsOn "def x: T := f (a -- c\n  ) -- d\n" == Some False)
      = True :=
  byComputing
