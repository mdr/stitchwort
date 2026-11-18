--| Each slice 1 expression hangs as an element (ticket 18h), for the expressions with no comments and no kept blank
--| lines (`Expr.quiet1`): an induction over `Expr` that assembles the rule-level lemmas (`bareAtomHangs`,
--| `prefixHangs`, `parenElHangs`, `listHangs`, `tupleHangs`, `appElHangs`, `binaryChainHangs`, `arrowChainHangs`) and
--| discharges their hypotheses (`ItemsHang`, `ArgsHang` with `huggedBracket`'s opened form, `LinkFacts`, `PairFacts`,
--| the operator's `RunOperator`, the bare arrow's `GluesAt`).
--|
--| The invariant (`ExprFacts`): a quiet slice 1 expression, wherever it stands (`around`), hangs as an element laid
--| at any indentation and seated at any column, after a waiting comment only where `around.before` says, trailing
--| nothing; and as a chain's operand at any level, its `LinkFacts` hold with no trailing comment. The second half is
--| carried because a chain's operands are read through `linkDocs`, which flattens the operands of the same level.
--|
--| The induction (`leadFacts`) is over the expressions quiet but for own-line comments above their first token
--| (`Expr.leadQuiet1`), wherever the element doesn't write them (`bareAt`: hoisted, or none); where it does, the
--| element starts after them (`Fmt.DeclFactsProofs.leadElHangs`). `ExprFacts` is the quiet case.
--|
--| Why quiet otherwise: a later token with comments above it, or any trailing comment, is not yet carried through
--| the rule-level lemmas, whose sub-elements' `ElHangs` start at `wordStart` and trail nothing (NOTES, SW-4045,
--| SW-4058).

namespace Fmt.ExprHangProofs
import Std (Bool, DecEq, Doc, Eq, List, Nat, Option, Text, Void)
import Std.Doc (..)
import Std.Doc.Proofs (..)
import Syntax (Comments, Expr, InfixKind, Note, Tok, Word)
import Fmt (..)
import Fmt.HangProofs (..)
import Fmt.MarkProofs (allKeysFrom, keysFrom)
import Fmt.AppHangProofs (ArgsHang, Hangs, appElHangs, argAround, lastArg)
import Fmt.ChainHangProofs (
  GluesAt,
  HangsAt,
  LinkFacts,
  PairFacts,
  RunOperator,
  arrowChainHangs,
  arrowLeafGlues,
  binaryChainHangs
)
import Fmt.BracketHangProofs (
  ItemsHang,
  groupedBracketHangs,
  huggedBracketIs,
  lastList,
  lastTrails,
  lastTuple,
  listHangs,
  parenElHangs,
  tupleHangs
)
import Fmt.DeclHangProofs (WordToken, bareAtomHangs)
import Fmt.SpellProofs (..)
import Fmt.TreeJoinProofs (
  lexKind,
  lexKindOfSpells,
  spellsNotComment,
  spellsNotLayout,
  spellsOfText1,
  spellsQuiet,
  wordQuiet
)

-- The class.

--| A token with no comments and no blank line kept above it.
def Word.quiet1 (word: Word): Bool := match word.comments with
  | { above = [], after = None, blankBefore = False } => True
  | _ => False

--| An expression whose every token is quiet, and whose calls each have an argument, as every call the parser reads
--| does.
def Expr.quiet1: Expr → Bool
  | Atom _ word => word.quiet1
  | Paren open inner close => open.quiet1 && inner.quiet1 && close.quiet1
  | Tuple open items _ close => open.quiet1 && allQuiet1 items && close.quiet1
  | ListOf open items _ close => open.quiet1 && allQuiet1 items && close.quiet1
  | App head arguments => !arguments.isEmpty && head.quiet1 && allQuiet1 arguments
  | Infix _ left operator right => left.quiet1 && operator.quiet1 && right.quiet1
  | Prefix operator operand => operator.quiet1 && operand.quiet1
  | _ => False

def allQuiet1: List Expr → Bool
  | [] => True
  | [expr, ..rest] => expr.quiet1 && allQuiet1 rest

--| A quiet token is the fixed word of its text.
theorem quietIs ∀ (word: Word) (quiet: word.quiet1 = True): word = fixedWord word.text Comments.none :=
  match word, quiet with | { text, comments = { above = [], after = None, blankBefore = False } }, _ => byComputing

theorem quietNoTrail ∀ (word: Word) (quiet: word.quiet1 = True): word.trails = False := match word, quiet with
  | { text, comments = { above = [], after = None, blankBefore = False } }, _ => byComputing

-- Lists of words.

theorem allAppend ∀ (front back: List Word)
    (first: front.all Word.quiet1 = True)
    (second: back.all Word.quiet1 = True):
    (front ++ back).all Word.quiet1 = True :=
  match front with
    | [] => second
    | [word, ..rest] => rewrite Bool.andLeft first, allAppend rest back (Bool.andRight first) second

theorem allReverse ∀ (words: List Word) (quiet: words.all Word.quiet1 = True): words.reverse.all Word.quiet1 = True :=
  match words with
    | [] => byComputing
    | [word, ..rest] =>
      rewrite List.reverseCons word rest then
        allAppend rest.reverse [word] (allReverse rest (Bool.andRight quiet)) (rewrite Bool.andLeft quiet)

theorem allDrop ∀ (words: List Word) (quiet: words.all Word.quiet1 = True): (words.drop 1).all Word.quiet1 = True :=
  match words with
    | [] => byComputing
    | [word, ..rest] => Bool.andRight quiet

--| Quiet words read back trail nothing.
theorem trailsBackQuiet ∀ (words: List Word) (quiet: words.all Word.quiet1 = True): trailsBack words = False :=
  match words with
    | [] => byComputing
    | [word, ..rest] =>
      rewrite quietNoTrail word (Bool.andLeft quiet),
          trailsBackQuiet rest (Bool.andRight quiet),
          Bool.andFalse (isCloserText word.text)

--| A quiet token's own-line comments are none, wherever it stands.
theorem quietLeading ∀ (word: Word) (around: Around) (key: Nat)
    (quiet: word.quiet1 = True):
    word.leading around key = [] :=
  match word, quiet with
    | { text, comments = { above = [], after = None, blankBefore = False } }, _ =>
      match around.hoisted, around.item with
        | True, _ => byComputing
        | False, True => byComputing
        | False, False => byComputing

-- The words of a quiet expression.

theorem quietWords ∀ (expr: Expr) (quiet: expr.quiet1 = True): expr.words.all Word.quiet1 = True :=
  match expr, quiet with
    | Atom _ word, quiet => rewrite quiet
    | Paren open inner close, quiet =>
      allAppend
        [open, ..inner.words]
        [close]
        (rewrite Bool.andLeft quiet then quietWords inner (Bool.andLeft (Bool.andRight quiet)))
        (rewrite Bool.andRight (Bool.andRight quiet))
    | Tuple open items _ close, quiet =>
      allAppend
        [open, ..itemsWords items]
        [close]
        (rewrite Bool.andLeft quiet then itemsQuiet items (Bool.andLeft (Bool.andRight quiet)))
        (rewrite Bool.andRight (Bool.andRight quiet))
    | ListOf open items _ close, quiet =>
      allAppend
        [open, ..itemsWords items]
        [close]
        (rewrite Bool.andLeft quiet then itemsQuiet items (Bool.andLeft (Bool.andRight quiet)))
        (rewrite Bool.andRight (Bool.andRight quiet))
    | App head arguments, quiet =>
      allAppend head.words
        (itemsWords arguments)
        (quietWords head (Bool.andLeft (Bool.andRight quiet)))
        (itemsQuiet arguments (Bool.andRight (Bool.andRight quiet)))
    | Infix _ left operator right, quiet =>
      allAppend left.words
        [operator, ..right.words]
        (quietWords left (Bool.andLeft quiet))
        (rewrite Bool.andLeft (Bool.andRight quiet) then quietWords right (Bool.andRight (Bool.andRight quiet)))
    | Prefix operator operand, quiet => rewrite Bool.andLeft quiet then quietWords operand (Bool.andRight quiet)

theorem itemsQuiet ∀ (items: List Expr) (quiet: allQuiet1 items = True): (itemsWords items).all Word.quiet1 = True :=
  match items with
    | [] => byComputing
    | [item, ..rest] =>
      allAppend item.words
        (itemsWords rest)
        (quietWords item (Bool.andLeft quiet))
        (itemsQuiet rest (Bool.andRight quiet))

--| A quiet expression trails no comment.
theorem quietTrails ∀ (expr: Expr) (quiet: expr.quiet1 = True): expr.trails = False :=
  trailsBackQuiet expr.words.reverse (allReverse expr.words (quietWords expr quiet))

--| A quiet bracket has no comment before its closer.
theorem quietBeforeClose ∀ (open: Word) (items: List Expr) (close: Word)
    (quiet: (ListOf open items False close).quiet1 = True):
    (ListOf open items False close).trailsBeforeClose = False :=
  let words := (ListOf open items False close).words
  trailsBackQuiet
    (words.reverse.drop 1)
    (allDrop words.reverse (allReverse words (quietWords (ListOf open items False close) quiet)))

--| A quiet expression's first token has no own-line comments, wherever it stands.
theorem firstLeading ∀ (expr: Expr) (around: Around) (key: Nat)
    (quiet: expr.quiet1 = True):
    expr.firstWord.leading around key = [] :=
  quietLeading expr.firstWord around key (headQuiet expr.words (quietWords expr quiet))

--| A quiet token has no own-line comments above it.
theorem wordQuietUnnoted ∀ (word: Word) (quiet: word.quiet1 = True): word.noted = False := match word, quiet with
  | { text, comments = { above = [], after = None, blankBefore = False } }, _ => byComputing

--| A quiet expression's first token has no own-line comments above it.
theorem quietNoted ∀ (expr: Expr) (quiet: expr.quiet1 = True): expr.noted = False :=
  wordQuietUnnoted expr.firstWord (headQuiet expr.words (quietWords expr quiet))

--| The first of quiet words is quiet, and so is the word that stands for none.
theorem headQuiet ∀ (words: List Word) (quiet: words.all Word.quiet1 = True): (words.headOr Word.none).quiet1 = True :=
  match words with
    | [] => byComputing
    | [word, ..rest] => Bool.andLeft quiet

--| The last of quiet arguments trails nothing.
theorem lastQuiet ∀ (argument: Expr) (rest: List Expr)
    (quiet: allQuiet1 [argument, ..rest] = True):
    (lastArg argument rest).trails = False :=
  match rest with
    | [] => quietTrails argument (Bool.andLeft quiet)
    | [next, ..more] => lastQuiet next more (Bool.andRight quiet)

--| After quiet items, nothing trails.
theorem lastTrailsQuiet ∀ (items: List Expr) (quiet: allQuiet1 items = True): lastTrails False items = False :=
  match items with
    | [] => byComputing
    | [item, ..rest] => rewrite quietTrails item (Bool.andLeft quiet) then lastTrailsQuiet rest (Bool.andRight quiet)

-- Tokens.

--| A token kind the fold takes as it takes a name, as a test.
def plainKind (kind: Tok): Bool :=
  !kind.isCloser && !kind.isOpener && !(kind == Comma) && !(kind == ColonEq) && !(kind == Colon) && !(kind == Arrow)

theorem plainOf ∀ (kind: Tok) (plain: plainKind kind = True): Fmt.HangProofs.Plain kind := (
  Bool.notTrue _ (Bool.andLeft plain),
  Bool.notTrue _ (Bool.andLeft (Bool.andRight plain)),
  Bool.notTrue _ (Bool.andLeft (Bool.andRight (Bool.andRight plain))),
  Bool.notTrue _ (Bool.andLeft (Bool.andRight (Bool.andRight (Bool.andRight plain)))),
  Bool.notTrue _ (Bool.andLeft (Bool.andRight (Bool.andRight (Bool.andRight (Bool.andRight plain))))),
  Bool.notTrue _ (Bool.andRight (Bool.andRight (Bool.andRight (Bool.andRight (Bool.andRight plain)))))
)

--| A text as the lexer reads it and the rules write it, as a test.
def wordText (text: Text): Bool := !text.startsWith "--" && !isLayout text && !isCloserText text && !(text == ",")

theorem wordTokenOf ∀ (text: Text) (word: wordText text = True): WordToken text := (
  Bool.notTrue _ (Bool.andLeft word),
  Bool.notTrue _ (Bool.andLeft (Bool.andRight word)),
  Bool.notTrue _ (Bool.andLeft (Bool.andRight (Bool.andRight word))),
  Bool.notTrue _ (Bool.andRight (Bool.andRight (Bool.andRight word)))
)

--| A name or numeral, as `within1` spells it, is a plain token.
theorem wordFacts ∀ (kind: Tok) (text: Text)
    (within: (kind.wordWithin1 && textSpells1 kind text) = True):
    Fmt.HangProofs.Plain (lexKind text) ∧ WordToken text :=
  let spells := spellsOfText1 kind text (Bool.andRight within)
  let (comma, closer) := spellsQuiet kind text spells (wordQuiet kind (Bool.andLeft within))
  let token := (spellsNotComment kind text spells, spellsNotLayout kind text spells, closer, comma)
  rewrite lexKindOfSpells kind text spells then
    match kind, within with
      | Lower, _ => (plainOf Lower byComputing, token)
      | Upper, _ => (plainOf Upper byComputing, token)
      | Num, _ => (plainOf Num byComputing, token)
      | Float, _ => (plainOf Float byComputing, token)

--| A prefix operator of slice 1 is a plain token.
theorem prefixToken ∀ (text: Text)
    (listed: prefixText1 text = True):
    Fmt.HangProofs.Plain (lexKind text) ∧ WordToken text :=
  match minus: text == "-" with
    | True => rewrite DecEq.sound minus then (plainOf _ byComputing, wordTokenOf _ byComputing)
    | False =>
      match bang: text == "!" with
        | True => rewrite DecEq.sound bang then (plainOf _ byComputing, wordTokenOf _ byComputing)
        | False =>
          match not: text == "¬" with
            | True => rewrite DecEq.sound not then (plainOf _ byComputing, wordTokenOf _ byComputing)

--| What an infix operator's token is: plain, or `->`.
def OperatorFacts (text: Text): Prop := (Fmt.HangProofs.Plain (lexKind text) ∨ lexKind text = Arrow) ∧ WordToken text

theorem plainOperator ∀ (text: Text)
    (plain: plainKind (lexKind text) = True)
    (word: wordText text = True):
    OperatorFacts text :=
  (Inl (plainOf (lexKind text) plain), wordTokenOf text word)

theorem arrowOperator ∀ (text: Text) (arrow: lexKind text = Arrow) (word: wordText text = True): OperatorFacts text :=
  (Inr arrow, wordTokenOf text word)

theorem operatorA ∀ (text: Text) (listed: operatorTextA1 text = True): OperatorFacts text := match a0: text == "->" with
  | True => rewrite DecEq.sound a0 then arrowOperator _ byComputing byComputing
  | False =>
    match a1: text == "→" with
      | True => rewrite DecEq.sound a1 then arrowOperator _ byComputing byComputing
      | False =>
        match a2: text == "||" with
          | True => rewrite DecEq.sound a2 then plainOperator _ byComputing byComputing
          | False =>
            match a3: text == "∨" with
              | True => rewrite DecEq.sound a3 then plainOperator _ byComputing byComputing
              | False =>
                match a4: text == "&&" with
                  | True => rewrite DecEq.sound a4 then plainOperator _ byComputing byComputing
                  | False =>
                    match a5: text == "∧" with
                      | True => rewrite DecEq.sound a5 then plainOperator _ byComputing byComputing

theorem operatorB ∀ (text: Text) (listed: operatorTextB1 text = True): OperatorFacts text := match a0: text == "+" with
  | True => rewrite DecEq.sound a0 then plainOperator _ byComputing byComputing
  | False =>
    match a1: text == "++" with
      | True => rewrite DecEq.sound a1 then plainOperator _ byComputing byComputing
      | False =>
        match a2: text == "-" with
          | True => rewrite DecEq.sound a2 then plainOperator _ byComputing byComputing
          | False =>
            match a3: text == "*" with
              | True => rewrite DecEq.sound a3 then plainOperator _ byComputing byComputing
              | False =>
                match a4: text == "/" with
                  | True => rewrite DecEq.sound a4 then plainOperator _ byComputing byComputing
                  | False =>
                    match a5: text == "%" with
                      | True => rewrite DecEq.sound a5 then plainOperator _ byComputing byComputing

theorem operatorC ∀ (text: Text) (listed: operatorTextC1 text = True): OperatorFacts text := match a0: text == "!=" with
  | True => rewrite DecEq.sound a0 then plainOperator _ byComputing byComputing
  | False =>
    match a1: text == "≠" with
      | True => rewrite DecEq.sound a1 then plainOperator _ byComputing byComputing
      | False =>
        match a2: text == "<" with
          | True => rewrite DecEq.sound a2 then plainOperator _ byComputing byComputing
          | False =>
            match a3: text == "<=" with
              | True => rewrite DecEq.sound a3 then plainOperator _ byComputing byComputing
              | False =>
                match a4: text == "≤" with
                  | True => rewrite DecEq.sound a4 then plainOperator _ byComputing byComputing

theorem operatorD ∀ (text: Text) (listed: operatorTextD1 text = True): OperatorFacts text := match a0: text == ">" with
  | True => rewrite DecEq.sound a0 then plainOperator _ byComputing byComputing
  | False =>
    match a1: text == ">=" with
      | True => rewrite DecEq.sound a1 then plainOperator _ byComputing byComputing
      | False =>
        match a2: text == "≥" with
          | True => rewrite DecEq.sound a2 then plainOperator _ byComputing byComputing
          | False =>
            match a3: text == "==" with
              | True => rewrite DecEq.sound a3 then plainOperator _ byComputing byComputing
              | False =>
                match a4: text == "=" with
                  | True => rewrite DecEq.sound a4 then plainOperator _ byComputing byComputing

theorem operatorFacts ∀ (text: Text) (listed: operatorText1 text = True): OperatorFacts text :=
  match a: operatorTextA1 text with
    | True => operatorA text a
    | False =>
      match b: operatorTextB1 text with
        | True => operatorB text b
        | False =>
          match c: operatorTextC1 text with
            | True => operatorC text c
            | False => operatorD text listed

--| `+`, `->` and `>` meet their operator lemmas' conditions.
theorem operatorWitnesses: OperatorFacts "+" ∧ OperatorFacts "->" ∧ OperatorFacts ">" ∧ OperatorFacts "→" := (
  operatorFacts "+" byComputing,
  arrowOperator "->" byComputing byComputing,
  operatorD ">" byComputing,
  operatorA "→" byComputing
)

--| A quiet infix operator of slice 1, after an operand that trails nothing, runs as a plain token or as `->`.
theorem quietRun ∀ (text: Text) (around: Around) (key: Nat)
    (listed: operatorText1 text = True):
    RunOperator lexKind False False ((fixedWord text Comments.none).leaf around key) :=
  let word := fixedWord text Comments.none
  let bare := quietLeading word around key byComputing
  let facts := operatorFacts text listed
  match facts with
    | (Inl plain, (notComment, solid, closer, comma)) => Inl (indent column =>
      elUnheld lexKind
        (word.leaf around key)
        indent
        column
        around.before
        False
        wordStart
        (plainLeafHangs lexKind word around key indent column plain notComment solid closer comma bare byComputing))
    | (Inr arrow, (notComment, solid, closer, comma)) => Inr (
      byComputing,
      arrowLeafGlues lexKind word around key False arrow notComment solid closer comma bare byComputing
    )

-- Shapes `within1` fixes.

--| A slice 1 expression in a paren is written as it is.
theorem parenInnerPlain ∀ (inner: Expr) (innerAround: Around)
    (within: inner.within1 = True):
    parenInner inner innerAround = inner.el innerAround :=
  match inner, within with
    | Atom _ _, _ => byComputing
    | Paren _ _ _, _ => byComputing
    | Tuple _ _ _ _, _ => byComputing
    | ListOf _ _ _ _, _ => byComputing
    | App _ _, _ => byComputing
    | Infix InfixBinary _ _ _, _ => byComputing
    | Infix InfixArrow _ _ _, _ => byComputing
    | Prefix _ _, _ => byComputing

--| A slice 1 operand after a chain's operator is a space and its links.
theorem chainRightPlain ∀ (level: Option Nat) (right: Expr) (rightAround: Around)
    (within: right.within1 = True):
    chainRight level right rightAround = [Doc.text " ", ..linkDocs level False right rightAround] :=
  match right, within with
    | Atom _ _, _ => byComputing
    | Paren _ _ _, _ => byComputing
    | Tuple _ _ _ _, _ => byComputing
    | ListOf _ _ _ _, _ => byComputing
    | App _ _, _ => byComputing
    | Infix InfixBinary _ _ _, _ => byComputing
    | Infix InfixArrow _ _ _, _ => byComputing
    | Prefix _ _, _ => byComputing

--| A slice 1 chain opens no arms: it has no `match`.
theorem opensNoArms ∀ (expr: Expr) (level: Option Nat) (within: expr.within1 = True): expr.opensArms level = False :=
  match expr, within with
    | Atom _ _, _ => byComputing
    | Paren _ _ _, _ => byComputing
    | Tuple _ _ _ _, _ => byComputing
    | ListOf _ _ _ _, _ => byComputing
    | App _ _, _ => byComputing
    | Infix InfixBinary left operator right, within =>
      rewrite opensNoArms left level (Bool.andLeft within),
          Bool.andFalse ((Infix InfixBinary left operator right).inChain level)
    | Infix InfixArrow left operator right, within =>
      rewrite opensNoArms left level (Bool.andLeft within),
          Bool.andFalse ((Infix InfixArrow left operator right).inChain level)
    | Prefix _ _, _ => byComputing

-- Comments above the first token.

--| A token with no comment after it and no blank line kept above it; it may have own-line comments above it.
def Word.lead1 (word: Word): Bool := match word.comments with
  | { above = _, after = None, blankBefore = False } => True
  | _ => False

--| A lead token's comments: those above it only.
def leadComments (above: List Note): Comments := { above, after = None, blankBefore = False }

--| An expression quiet but for own-line comments above its first token (`Expr.lead`), as a declaration's type or
--| value may have them.
def Expr.leadQuiet1: Expr → Bool
  | Atom _ word => word.lead1
  | Paren open inner close => open.lead1 && inner.quiet1 && close.quiet1
  | Tuple open items _ close => open.lead1 && allQuiet1 items && close.quiet1
  | ListOf open items _ close => open.lead1 && allQuiet1 items && close.quiet1
  | App head arguments => !arguments.isEmpty && head.leadQuiet1 && allQuiet1 arguments
  | Infix _ left operator right => left.leadQuiet1 && operator.quiet1 && right.quiet1
  | Prefix operator operand => operator.lead1 && operand.quiet1
  | _ => False

--| Where the first token's own-line comments are written elsewhere (`hoisted`), or it has none: as for a quiet
--| expression, the element writes no comments above its first token.
def Expr.bareAt (expr: Expr) (around: Around): Bool := around.hoisted || !expr.lead.noted

theorem leadIs ∀ (word: Word)
    (lead: word.lead1 = True):
    word = fixedWord word.text (leadComments word.comments.above) :=
  match word, lead with | { text, comments = { above, after = None, blankBefore = False } }, _ => byComputing

theorem quietWordLead ∀ (word: Word) (quiet: word.quiet1 = True): word.lead1 = True := match word, quiet with
  | { text, comments = { above = [], after = None, blankBefore = False } }, _ => byComputing

theorem leadNoTrail ∀ (word: Word) (lead: word.lead1 = True): word.trails = False := match word, lead with
  | { text, comments = { above, after = None, blankBefore = False } }, _ => byComputing

--| A lead token writes no own-line comments where they are written elsewhere or it has none.
theorem leadLeading ∀ (word: Word) (around: Around) (key: Nat)
    (lead: word.lead1 = True)
    (bare: (around.hoisted || !word.noted) = True):
    word.leading around key = [] :=
  match word, lead with
    | { text, comments = { above, after = None, blankBefore = False } }, _ =>
      match hoisted: around.hoisted, above with
        | True, _ => byComputing
        | False, [] =>
          match around.item with
            | True => byComputing
            | False => byComputing

theorem quietLead ∀ (expr: Expr) (quiet: expr.quiet1 = True): expr.leadQuiet1 = True := match expr, quiet with
  | Atom _ word, quiet => quietWordLead word quiet
  | Paren open inner close, quiet => rewrite quietWordLead open (Bool.andLeft quiet), Bool.andRight quiet
  | Tuple open items _ close, quiet => rewrite quietWordLead open (Bool.andLeft quiet), Bool.andRight quiet
  | ListOf open items _ close, quiet => rewrite quietWordLead open (Bool.andLeft quiet), Bool.andRight quiet
  | App head arguments, quiet =>
    rewrite Bool.andLeft quiet, quietLead head (Bool.andLeft (Bool.andRight quiet)), Bool.andRight (Bool.andRight quiet)
  | Infix _ left operator right, quiet => rewrite quietLead left (Bool.andLeft quiet), Bool.andRight quiet
  | Prefix operator operand, quiet => rewrite quietWordLead operator (Bool.andLeft quiet), Bool.andRight quiet

--| A quiet expression's first token has no own-line comments above it.
theorem quietUnnoted ∀ (expr: Expr) (quiet: expr.quiet1 = True): expr.lead.noted = False := match expr, quiet with
  | Atom _ word, quiet => wordQuietUnnoted word quiet
  | Paren open inner close, quiet => wordQuietUnnoted open (Bool.andLeft quiet)
  | Tuple open items _ close, quiet => wordQuietUnnoted open (Bool.andLeft quiet)
  | ListOf open items _ close, quiet => wordQuietUnnoted open (Bool.andLeft quiet)
  | App head arguments, quiet => quietUnnoted head (Bool.andLeft (Bool.andRight quiet))
  | Infix _ left operator right, quiet => quietUnnoted left (Bool.andLeft quiet)
  | Prefix operator operand, quiet => wordQuietUnnoted operator (Bool.andLeft quiet)

theorem unnotedBare ∀ (expr: Expr) (around: Around) (unnoted: expr.lead.noted = False): expr.bareAt around = True :=
  match hoisted: around.hoisted with
    | True => byComputing
    | False => rewrite unnoted

--| A lead token with no comments above it is quiet.
theorem wordLeadQuiet ∀ (word: Word) (lead: word.lead1 = True) (unnoted: word.noted = False): word.quiet1 = True :=
  match word, lead with
    | { text, comments = { above, after = None, blankBefore = False } }, _ =>
      match above, unnoted with
        | [], _ => byComputing
        | [note, ..rest], never => (Bool.trueNotFalse never).impossible

--| An expression quiet but for comments above its first token, with none there, is quiet.
theorem leadUnnotedQuiet ∀ (expr: Expr)
    (lead: expr.leadQuiet1 = True)
    (unnoted: expr.lead.noted = False):
    expr.quiet1 = True :=
  match expr, lead with
    | Atom _ word, lead => wordLeadQuiet word lead unnoted
    | Paren open inner close, lead => rewrite wordLeadQuiet open (Bool.andLeft lead) unnoted, Bool.andRight lead
    | Tuple open items _ close, lead => rewrite wordLeadQuiet open (Bool.andLeft lead) unnoted, Bool.andRight lead
    | ListOf open items _ close, lead => rewrite wordLeadQuiet open (Bool.andLeft lead) unnoted, Bool.andRight lead
    | App head arguments, lead =>
      rewrite Bool.andLeft lead,
          leadUnnotedQuiet head (Bool.andLeft (Bool.andRight lead)) unnoted,
          Bool.andRight (Bool.andRight lead)
    | Infix _ left operator right, lead => rewrite leadUnnotedQuiet left (Bool.andLeft lead) unnoted, Bool.andRight lead
    | Prefix operator operand, lead => rewrite wordLeadQuiet operator (Bool.andLeft lead) unnoted, Bool.andRight lead

theorem quietBare ∀ (expr: Expr) (around: Around) (quiet: expr.quiet1 = True): expr.bareAt around = True :=
  unnotedBare expr around (quietUnnoted expr quiet)

--| The first token of an expression quiet but for comments above it is a lead token.
theorem leadOfLead ∀ (expr: Expr) (lead: expr.leadQuiet1 = True): expr.lead.lead1 = True := match expr, lead with
  | Atom _ word, lead => lead
  | Paren open inner close, lead => Bool.andLeft lead
  | Tuple open items _ close, lead => Bool.andLeft lead
  | ListOf open items _ close, lead => Bool.andLeft lead
  | App head arguments, lead => leadOfLead head (Bool.andLeft (Bool.andRight lead))
  | Infix _ left operator right, lead => leadOfLead left (Bool.andLeft lead)
  | Prefix operator operand, lead => Bool.andLeft lead

--| Lead tokens trail nothing.
theorem leadAppend ∀ (front back: List Word)
    (first: front.all Word.lead1 = True)
    (second: back.all Word.lead1 = True):
    (front ++ back).all Word.lead1 = True :=
  match front with
    | [] => second
    | [word, ..rest] => rewrite Bool.andLeft first, leadAppend rest back (Bool.andRight first) second

theorem leadReverse ∀ (words: List Word) (lead: words.all Word.lead1 = True): words.reverse.all Word.lead1 = True :=
  match words with
    | [] => byComputing
    | [word, ..rest] =>
      rewrite List.reverseCons word rest then
        leadAppend rest.reverse [word] (leadReverse rest (Bool.andRight lead)) (rewrite Bool.andLeft lead)

theorem quietAllLead ∀ (words: List Word) (quiet: words.all Word.quiet1 = True): words.all Word.lead1 = True :=
  match words with
    | [] => byComputing
    | [word, ..rest] => rewrite quietWordLead word (Bool.andLeft quiet), quietAllLead rest (Bool.andRight quiet)

theorem trailsBackLead ∀ (words: List Word) (lead: words.all Word.lead1 = True): trailsBack words = False :=
  match words with
    | [] => byComputing
    | [word, ..rest] =>
      rewrite leadNoTrail word (Bool.andLeft lead),
          trailsBackLead rest (Bool.andRight lead),
          Bool.andFalse (isCloserText word.text)

theorem leadWords ∀ (expr: Expr) (lead: expr.leadQuiet1 = True): expr.words.all Word.lead1 = True :=
  match expr, lead with
    | Atom _ word, lead => rewrite lead
    | Paren open inner close, lead =>
      leadAppend
        [open, ..inner.words]
        [close]
        (rewrite Bool.andLeft lead then quietAllLead inner.words (quietWords inner (Bool.andLeft (Bool.andRight lead))))
        (rewrite quietWordLead close (Bool.andRight (Bool.andRight lead)))
    | Tuple open items _ close, lead =>
      leadAppend
        [open, ..itemsWords items]
        [close]
        (rewrite Bool.andLeft lead then
          quietAllLead (itemsWords items) (itemsQuiet items (Bool.andLeft (Bool.andRight lead))))
        (rewrite quietWordLead close (Bool.andRight (Bool.andRight lead)))
    | ListOf open items _ close, lead =>
      leadAppend
        [open, ..itemsWords items]
        [close]
        (rewrite Bool.andLeft lead then
          quietAllLead (itemsWords items) (itemsQuiet items (Bool.andLeft (Bool.andRight lead))))
        (rewrite quietWordLead close (Bool.andRight (Bool.andRight lead)))
    | App head arguments, lead =>
      leadAppend head.words
        (itemsWords arguments)
        (leadWords head (Bool.andLeft (Bool.andRight lead)))
        (quietAllLead (itemsWords arguments) (itemsQuiet arguments (Bool.andRight (Bool.andRight lead))))
    | Infix _ left operator right, lead =>
      leadAppend left.words
        [operator, ..right.words]
        (leadWords left (Bool.andLeft lead))
        (quietAllLead
          [operator, ..right.words]
          (rewrite Bool.andLeft (Bool.andRight lead) then quietWords right (Bool.andRight (Bool.andRight lead))))
    | Prefix operator operand, lead =>
      rewrite Bool.andLeft lead then quietAllLead operand.words (quietWords operand (Bool.andRight lead))

theorem leadDrop ∀ (words: List Word) (lead: words.all Word.lead1 = True): (words.drop 1).all Word.lead1 = True :=
  match words with
    | [] => byComputing
    | [word, ..rest] => Bool.andRight lead

--| A bracket quiet but for comments above its opener has no comment before its closer.
theorem leadBeforeClose ∀ (open: Word) (items: List Expr) (close: Word)
    (lead: (ListOf open items False close).leadQuiet1 = True):
    (ListOf open items False close).trailsBeforeClose = False :=
  let words := (ListOf open items False close).words
  trailsBackLead
    (words.reverse.drop 1)
    (leadDrop words.reverse (leadReverse words (leadWords (ListOf open items False close) lead)))

--| An expression quiet but for comments above its first token trails no comment.
theorem leadTrails ∀ (expr: Expr) (lead: expr.leadQuiet1 = True): expr.trails = False :=
  trailsBackLead expr.words.reverse (leadReverse expr.words (leadWords expr lead))

-- Brackets' marks.

--| Every quiet slice 1 expression's document has its `Mark` and `CloserLine` keys at least `low`; it has none, as
--| only comments make them. Named here and taken by the induction, which `Fmt.QuietKeyProofs.quietKeys` proves.
def QuietKeys: Prop :=
  ∀ (expr: Expr) (around: Around) (low: Nat) => expr.within1 = True
    → expr.quiet1 = True
    → keysFrom low (expr.el around) = True

theorem filterKeys ∀ (low: Nat) (docs: List Doc) (keep: Doc → Bool)
    (all: allKeysFrom low docs = True):
    allKeysFrom low (docs.filter keep) = True :=
  match docs with
    | [] => byComputing
    | [doc, ..rest] =>
      let later := filterKeys low rest keep (Bool.andRight all)
      match kept: keep doc with
        | True => rewrite Bool.andLeft all, later
        | False => later

--| `Doc.concat` leaves out empty documents, so it keeps their keys.
theorem keysConcat ∀ (low: Nat) (docs: List Doc)
    (all: allKeysFrom low docs = True):
    keysFrom low (Doc.concat docs) = True :=
  let kept := filterKeys low docs (doc => not doc.isEmpty) all
  match filtered: docs.filter (doc => not doc.isEmpty) with
    | [] => byComputing
    | [only] => Bool.andLeft kept
    | several => kept

theorem cellsKeys ∀ (items: List Expr) (low: Nat) (bare arm before: Bool) (at: Nat)
    (within: allWithin1 items = True)
    (quiet: allQuiet1 items = True) (keys: QuietKeys):
    allKeysFrom low (cells bare arm before at items) = True :=
  match items with
    | [] => byComputing
    | [item] => rewrite keys item (firstAround bare arm before at) low (Bool.andLeft within) (Bool.andLeft quiet)
    | [item, next, ..more] =>
      let one := keys item (firstAround bare arm before at) low (Bool.andLeft within) (Bool.andLeft quiet)
      rewrite keysConcat low [item.el (firstAround bare arm before at), Closing ","] (rewrite one),
          cellsKeys
            [next, ..more]
            low
            False
            arm
            item.trails
            (at + item.size)
            (Bool.andRight within)
            (Bool.andRight quiet)
            keys

theorem brokenKeys ∀ (items: List Expr) (low: Nat) (bare arm first before: Bool) (at: Nat)
    (within: allWithin1 items = True)
    (quiet: allQuiet1 items = True) (keys: QuietKeys):
    allKeysFrom low (brokenItems bare arm first before at items) = True :=
  match items with
    | [] => byComputing
    | [item] =>
      match first with
        | True => rewrite keys item (firstAround bare arm before at) low (Bool.andLeft within) (Bool.andLeft quiet)
        | False => rewrite keys item (firstAround bare arm before at) low (Bool.andLeft within) (Bool.andLeft quiet)
    | [item, next, ..more] =>
      let rest :=
        brokenKeys
          [next, ..more]
          low
          False
          arm
          False
          item.trails
          (at + item.size)
          (Bool.andRight within)
          (Bool.andRight quiet)
          keys
      match first with
        | True =>
          rewrite keys item (firstAround bare arm before at) low (Bool.andLeft within) (Bool.andLeft quiet), rest
        | False =>
          rewrite keys item (firstAround bare arm before at) low (Bool.andLeft within) (Bool.andLeft quiet), rest

-- The induction.

--| What the induction carries (the invariant): the expression hangs as an element wherever it stands, trailing
--| nothing, and as a chain's operand at any level.
def ExprFacts (expr: Expr): Prop :=
  (∀ (around: Around) => HangsAt lexKind around.before False (expr.el around))
    ∧ (∀ (level: Option Nat) (first: Bool) (around: Around) => LinkFacts lexKind level first expr around False)

--| The invariant for an expression quiet but for comments above its first token: as `ExprFacts`, where the element
--| writes no comments above its first token (`bareAt`).
def LeadFacts (expr: Expr): Prop :=
  (∀ (around: Around) => expr.bareAt around = True → HangsAt lexKind around.before False (expr.el around))
    ∧ (∀ (level: Option Nat) (first: Bool) (around: Around) => expr.bareAt around = True
      → LinkFacts lexKind level first expr around False)

theorem leadHangsOf ∀ (expr: Expr)
    (facts: LeadFacts expr) (around: Around)
    (bare: expr.bareAt around = True):
    HangsAt lexKind around.before False (expr.el around) :=
  let (hangs, _) := facts
  hangs around bare

theorem leadLinksOf ∀ (expr: Expr)
    (facts: LeadFacts expr)
    (level: Option Nat) (first: Bool) (around: Around)
    (bare: expr.bareAt around = True):
    LinkFacts lexKind level first expr around False :=
  let (_, links) := facts
  links level first around bare

theorem hangsOf ∀ (expr: Expr)
    (facts: ExprFacts expr) (around: Around):
    HangsAt lexKind around.before False (expr.el around) :=
  let (hangs, _) := facts
  hangs around

theorem linksOf ∀ (expr: Expr)
    (facts: ExprFacts expr)
    (level: Option Nat) (first: Bool) (around: Around):
    LinkFacts lexKind level first expr around False :=
  let (_, links) := facts
  links level first around

theorem openParen: OpenerToken lexKind "(" := (
  byComputing,
  byComputing,
  byComputing,
  byComputing,
  byComputing,
  byComputing,
  byComputing,
  byComputing,
  byComputing,
  byComputing
)

theorem openBracket: OpenerToken lexKind "[" := (
  byComputing,
  byComputing,
  byComputing,
  byComputing,
  byComputing,
  byComputing,
  byComputing,
  byComputing,
  byComputing,
  byComputing
)

theorem closeParen: CloserToken lexKind ")" := (byComputing, byComputing, byComputing, byComputing, byComputing)

theorem closeBracket: CloserToken lexKind "]" := (byComputing, byComputing, byComputing, byComputing, byComputing)

--| An element that trails nothing, by an equation.
theorem elQuiet ∀ (kinds: Text → Tok) (doc: Doc) (indent column: Nat)
    (before trails: Bool) (start: Nat → Place → Option Nat)
    (el: ElHangs kinds doc indent column before trails start)
    (quiet: trails = False):
    ElHangs kinds doc indent column before False start :=
  match trails, quiet with | False, _ => el

--| A slice 1 paren as a call's last argument is written as it is, with no hug.
theorem parenLast ∀ (open: Word) (inner: Expr) (close: Word) (around: Around)
    (within: inner.within1 = True):
    lastArgument (Paren open inner close) around = ((Paren open inner close).el around, None) :=
  match inner, within with
    | Atom _ _, _ => byComputing
    | Paren _ _ _, _ => byComputing
    | Tuple _ _ _ _, _ => byComputing
    | ListOf _ _ _ _, _ => byComputing
    | App _ _, _ => byComputing
    | Infix InfixBinary _ _ _, _ => byComputing
    | Infix InfixArrow _ _ _, _ => byComputing
    | Prefix _ _, _ => byComputing

--| Quiet items of a slice 1 bracket each hang, after an opener that trails nothing.
theorem itemsHang ∀ (items: List Expr) (inset: Nat) (bare arm: Bool) (at: Nat)
    (within: allWithin1 items = True)
    (lexical: allLexical1 items = True)
    (quiet: allQuiet1 items = True) (keys: QuietKeys):
    ItemsHang lexKind inset bare arm False False at items :=
  match items with
    | [] => byComputing
    | [item, ..rest] =>
      let facts :=
        leadFacts item (Bool.andLeft within) (Bool.andLeft lexical) (quietLead item (Bool.andLeft quiet)) keys
      let quietItem := quietTrails item (Bool.andLeft quiet)
      let first: ElHangs lexKind (item.el (firstAround bare arm False at)) inset inset False item.trails wordStart :=
        rewrite quietItem then
          leadHangsOf item facts
            (firstAround bare arm False at)
            (quietBare item (firstAround bare arm False at) (Bool.andLeft quiet))
            inset
            inset
      let later: ItemsHang lexKind inset False arm item.trails item.trails (at + item.size) rest :=
        rewrite quietItem then
          itemsHang rest inset False arm
            (at + item.size)
            (Bool.andRight within)
            (Bool.andRight lexical)
            (Bool.andRight quiet)
            keys
      (first, later)

--| A quiet bracket hugged as a call's last argument: as `huggedBracket` writes it, and opened.
--|
--| Proof idea: the bracket's parts in a group, broken or not (`groupedBracketHangs`), whose items hang
--| (`itemsHang`) and whose keys are the items' (`cellsKeys`, `brokenKeys`); nothing trails before the closer.
theorem hugFacts ∀ (list: Bool) (open: Word) (items: List Expr) (close: Word) (around: Around)
    (lexical: allLexical1 items = True)
    (within: allWithin1 items = True)
    (quiet: (ListOf open items False close).quiet1 = True)
    (isOpen: open.text = (if list then "[" else "("))
    (isClose: close.text = (if list then "]" else ")")) (keys: QuietKeys):
    Hangs lexKind False False (huggedBracket list open items close around).fst
      ∧ (∀ (opened: Doc) => (huggedBracket list open items close around).snd = Some opened
        → Hangs lexKind False False opened) :=
  let openWord := fixedWord open.text Comments.none
  let closeWord := fixedWord close.text Comments.none
  let itemsQuietly: allQuiet1 items = True := Bool.andLeft (Bool.andRight quiet)
  let beforeClose := quietBeforeClose openWord items closeWord (rewrite itemsQuietly)
  let bare := quietLeading openWord around around.at byComputing
  let opener: OpenerToken lexKind openWord.text := match list with
    | True => rewrite isOpen then openBracket
    | False => rewrite isOpen then openParen
  let closer: CloserToken lexKind closeWord.text := match list with
    | True => rewrite isClose then closeBracket
    | False => rewrite isClose then closeParen
  let bareItems := list && items.all Expr.plainItem
  let lays: ∀ (hard: Bool) => Hangs lexKind False False
    (Group (bracketContent list openWord items closeWord { around | hoisted = True }) hard) :=
    hard inset =>
      let el :=
        groupedBracketHangs lexKind list openWord items closeWord around hard inset inset opener byComputing closer
            byComputing byComputing byComputing
            (itemsHang items (inset + 2) bareItems around.inArm (around.at + 1) within lexical itemsQuietly keys)
            (cellsKeys items (around.at + 1) bareItems around.inArm False (around.at + 1) within itemsQuietly keys)
            (brokenKeys items
              (around.at + 1)
              bareItems
              around.inArm
              True
              False
              (around.at + 1)
              within
              itemsQuietly
              keys)
            (never => (Bool.falseNotTrue (Eq.trans (lastTrailsQuiet items itemsQuietly).flipped never)).impossible)
      elQuiet lexKind _ inset inset False _ wordStart el beforeClose
  rewrite quietIs open (Bool.andLeft quiet),
      quietIs close (Bool.andRight (Bool.andRight quiet)),
      huggedBracketIs list openWord items closeWord around bare then
    (
      lays (bracketContent list openWord items closeWord { around | hoisted = True }).forcesBreak,
      opened same => rewrite <- Option.someInjective same then lays True
    )

--| A quiet slice 1 call's last argument hangs, as it is and opened, after an element that trails nothing.
theorem lastHangs ∀ (argument: Expr) (around: Around)
    (quietBefore: around.before = False)
    (within: argument.within1 = True)
    (lexical: argument.lexical1 = True)
    (quiet: argument.quiet1 = True) (keys: QuietKeys):
    Hangs lexKind around.before False (lastArgument argument around).fst
      ∧ (∀ (opened: Doc) => (lastArgument argument around).snd = Some opened
        → Hangs lexKind around.before False opened) :=
  let facts := leadFacts argument within lexical (quietLead argument quiet) keys
  let plain: Hangs lexKind around.before False (argument.el around) := inset =>
    leadHangsOf argument facts around (quietBare argument around quiet) inset inset
  match argument, within with
    | Atom _ _, _ => (plain, opened never => cases)
    | Paren open inner close, within =>
      rewrite parenLast open inner close around within then (plain, opened never => cases)
    | App _ _, _ => (plain, opened never => cases)
    | Infix InfixBinary _ _ _, _ => (plain, opened never => cases)
    | Infix InfixArrow _ _ _, _ => (plain, opened never => cases)
    | Prefix _ _, _ => (plain, opened never => cases)
    | Tuple open items trailing close, within =>
      rewrite quietBefore then
        hugFacts False open items close around
          (Bool.andRight (Bool.andRight lexical))
          within
          quiet
          (DecEq.sound (Bool.andLeft lexical))
          (DecEq.sound (Bool.andLeft (Bool.andRight lexical)))
          keys
    | ListOf open items trailing close, within =>
      rewrite quietBefore then
        hugFacts True open items close around
          (Bool.andRight (Bool.andRight lexical))
          within
          quiet
          (DecEq.sound (Bool.andLeft lexical))
          (DecEq.sound (Bool.andLeft (Bool.andRight lexical)))
          keys

--| Quiet arguments of a slice 1 call each hang, the last as it is and opened, after an element that trails nothing.
theorem argsHang ∀ (arm: Bool) (previous: Expr) (at: Nat) (arguments: List Expr)
    (previousQuiet: previous.trails = False)
    (within: allWithin1 arguments = True)
    (lexical: allLexical1 arguments = True)
    (quiet: allQuiet1 arguments = True) (keys: QuietKeys):
    ArgsHang lexKind arm previous at arguments :=
  match arguments with
    | [] => byComputing
    | [argument] =>
      rewrite quietTrails argument (Bool.andLeft quiet) then
        lastHangs argument
          (argAround arm previous at)
          previousQuiet
          (Bool.andLeft within)
          (Bool.andLeft lexical)
          (Bool.andLeft quiet)
          keys
    | [argument, next, ..more] =>
      let argumentQuiet := quietTrails argument (Bool.andLeft quiet)
      let facts :=
        leadFacts argument (Bool.andLeft within) (Bool.andLeft lexical) (quietLead argument (Bool.andLeft quiet)) keys
      let first: Hangs lexKind previous.trails argument.trails (argument.el (argAround arm previous at)) :=
        rewrite argumentQuiet then
          (inset =>
            leadHangsOf argument facts
              (argAround arm previous at)
              (quietBare argument (argAround arm previous at) (Bool.andLeft quiet))
              inset
              inset)
      (
        first,
        argsHang arm argument
          (at + argument.size)
          [next, ..more]
          argumentQuiet
          (Bool.andRight within)
          (Bool.andRight lexical)
          (Bool.andRight quiet)
          keys
      )

--| Each slice 1 expression quiet but for comments above its first token hangs as an element wherever it writes no
--| comments above that token (`bareAt`: they are written elsewhere, or there are none), and as a chain's operand.
--|
--| Proof idea: by the expression, each case its rule-level lemma: a name or numeral `plainLeafHangs`; a prefix
--| `prefixHangs` on its operand's; a paren `parenElHangs` (its opener trails nothing); a list or tuple `listHangs` or
--| `tupleHangs` with `itemsHang`; a call `appElHangs` with `argsHang` (the last argument as `huggedBracket` writes it,
--| `hugFacts`); a chain `binaryChainHangs` or `arrowChainHangs`, whose `PairFacts` are the operands' `LinkFacts`
--| (the second half of the invariant) and the operator's `quietRun`. An operand that is a chain of the chain's level
--| gives its `LinkFacts` from its own operands'; anything else's are its element facts. Only the first token, the
--| call's head's or the chain's first operand's, may have comments above it; it shares `bareAt` with the expression,
--| and the rest are quiet, so bare anywhere.
theorem leadFacts ∀ (expr: Expr)
    (within: expr.within1 = True)
    (lexical: expr.lexical1 = True)
    (lead: expr.leadQuiet1 = True) (keys: QuietKeys):
    LeadFacts expr :=
  match expr, within with
    | Atom kind word, within =>
      let (plain, (notComment, solid, closer, comma)) := wordFacts kind word.text within
      let fixed := fixedWord word.text (leadComments word.comments.above)
      let hangs: ∀ (around: Around) => (Atom kind fixed).bareAt around = True
        → HangsAt lexKind around.before False ((Atom kind fixed).el around) :=
        around bare indent column =>
          plainLeafHangs lexKind fixed around around.at indent column plain notComment solid closer comma
            (leadLeading fixed around around.at byComputing bare)
            byComputing
      rewrite leadIs word lead then (hangs, level first around bare => hangs around bare)
    | Prefix operator operand, within =>
      let word := fixedWord operator.text (leadComments operator.comments.above)
      let (plain, (notComment, solid, closer, comma)) := prefixToken operator.text (Bool.andRight within)
      let operandQuiet: operand.quiet1 = True := Bool.andRight lead
      let inner := leadFacts operand (Bool.andLeft within) (Bool.andRight lexical) (quietLead operand operandQuiet) keys
      let hangs: ∀ (around: Around) => (Prefix word operand).bareAt around = True
        → HangsAt lexKind around.before False ((Prefix word operand).el around) :=
        around bare indent column =>
          prefixHangs lexKind word operand around indent column False plain notComment solid closer comma
            (leadLeading word around around.at byComputing bare)
            byComputing
            (inset =>
              leadHangsOf operand inner
                (around.next False 1)
                (quietBare operand (around.next False 1) operandQuiet)
                inset
                inset)
      rewrite leadIs operator (Bool.andLeft lead) then (hangs, level first around bare => hangs around bare)
    | Paren open inner close, within =>
      let openWord := fixedWord open.text (leadComments open.comments.above)
      let closeWord := fixedWord close.text Comments.none
      let isOpen: open.text = "(" := DecEq.sound (Bool.andLeft lexical)
      let isClose: close.text = ")" := DecEq.sound (Bool.andLeft (Bool.andRight lexical))
      let innerQuiet := Bool.andLeft (Bool.andRight lead)
      let facts := leadFacts inner within (Bool.andRight (Bool.andRight lexical)) (quietLead inner innerQuiet) keys
      let hangs: ∀ (around: Around) => (Paren openWord inner closeWord).bareAt around = True
        → HangsAt lexKind around.before False ((Paren openWord inner closeWord).el around) :=
        around bare indent column =>
          let el :=
            parenElHangs lexKind openWord inner closeWord around indent column
              (rewrite isOpen then openParen)
              byComputing
              byComputing
              (rewrite isClose then closeParen)
              byComputing
              byComputing
              (leadLeading openWord around around.at byComputing bare)
              (parenInnerPlain inner (around.next False 1) within)
              (inset =>
                rewrite quietTrails inner innerQuiet then
                  leadHangsOf inner facts
                    (around.next False 1)
                    (quietBare inner (around.next False 1) innerQuiet)
                    inset
                    inset)
              (keys inner (around.next False 1) (around.at + 1) within innerQuiet)
          elQuiet lexKind _ indent column around.before _ wordStart el (quietTrails inner innerQuiet)
      rewrite leadIs open (Bool.andLeft lead), quietIs close (Bool.andRight (Bool.andRight lead)) then
        (hangs, level first around bare => hangs around bare)
    | ListOf open items trailing close, within =>
      let openWord := fixedWord open.text (leadComments open.comments.above)
      let closeWord := fixedWord close.text Comments.none
      let isOpen: open.text = "[" := DecEq.sound (Bool.andLeft lexical)
      let isClose: close.text = "]" := DecEq.sound (Bool.andLeft (Bool.andRight lexical))
      let itemsLexical := Bool.andRight (Bool.andRight lexical)
      let itemsQuietly: allQuiet1 items = True := Bool.andLeft (Bool.andRight lead)
      let beforeClose := leadBeforeClose openWord items closeWord (rewrite itemsQuietly)
      let bareItems := True && items.all Expr.plainItem
      let hangs: ∀ (around: Around) => (ListOf openWord items trailing closeWord).bareAt around = True
        → HangsAt lexKind around.before False ((ListOf openWord items trailing closeWord).el around) :=
        around bare indent column =>
          let el :=
            listHangs lexKind openWord items trailing closeWord around indent column
              (rewrite isOpen then openBracket)
              byComputing
              (rewrite isClose then closeBracket)
              byComputing
              byComputing
              byComputing
              (leadLeading openWord around around.at byComputing bare)
              (deep =>
                itemsHang items (deep + 2) bareItems around.inArm (around.at + 1) within itemsLexical itemsQuietly keys)
              (cellsKeys items (around.at + 1) bareItems around.inArm False (around.at + 1) within itemsQuietly keys)
              (brokenKeys items
                (around.at + 1)
                bareItems
                around.inArm
                True
                False
                (around.at + 1)
                within
                itemsQuietly
                keys)
              (never => (Bool.falseNotTrue (Eq.trans (lastTrailsQuiet items itemsQuietly).flipped never)).impossible)
          elQuiet lexKind _ indent column around.before _ wordStart el beforeClose
      rewrite leadIs open (Bool.andLeft lead), quietIs close (Bool.andRight (Bool.andRight lead)) then
        (hangs, level first around bare => hangs around bare)
    | Tuple open items trailing close, within =>
      let openWord := fixedWord open.text (leadComments open.comments.above)
      let closeWord := fixedWord close.text Comments.none
      let isOpen: open.text = "(" := DecEq.sound (Bool.andLeft lexical)
      let isClose: close.text = ")" := DecEq.sound (Bool.andLeft (Bool.andRight lexical))
      let itemsLexical := Bool.andRight (Bool.andRight lexical)
      let itemsQuietly: allQuiet1 items = True := Bool.andLeft (Bool.andRight lead)
      let beforeClose := leadBeforeClose openWord items closeWord (rewrite itemsQuietly)
      let hangs: ∀ (around: Around) => (Tuple openWord items trailing closeWord).bareAt around = True
        → HangsAt lexKind around.before False ((Tuple openWord items trailing closeWord).el around) :=
        around bare indent column =>
          let el :=
            tupleHangs lexKind openWord items trailing closeWord around indent column
              (rewrite isOpen then openParen)
              byComputing
              (rewrite isClose then closeParen)
              byComputing
              byComputing
              byComputing
              (leadLeading openWord around around.at byComputing bare)
              (deep =>
                itemsHang items (deep + 2) False around.inArm (around.at + 1) within itemsLexical itemsQuietly keys)
              (cellsKeys items (around.at + 1) False around.inArm False (around.at + 1) within itemsQuietly keys)
              (brokenKeys items (around.at + 1) False around.inArm True False (around.at + 1) within itemsQuietly keys)
              (never => (Bool.falseNotTrue (Eq.trans (lastTrailsQuiet items itemsQuietly).flipped never)).impossible)
          elQuiet lexKind _ indent column around.before _ wordStart el beforeClose
      rewrite leadIs open (Bool.andLeft lead), quietIs close (Bool.andRight (Bool.andRight lead)) then
        (hangs, level first around bare => hangs around bare)
    | App head arguments, within =>
      match arguments, lead with
        | [], never => (Bool.falseNotTrue never).impossible
        | [argument, ..rest], lead =>
          let headLead: head.leadQuiet1 = True := Bool.andLeft lead
          let argumentsQuiet: allQuiet1 [argument, ..rest] = True := Bool.andRight lead
          let headFacts := leadFacts head (Bool.andLeft within) (Bool.andLeft lexical) headLead keys
          let headTrails := leadTrails head headLead
          let hangs: ∀ (around: Around) => (App head [argument, ..rest]).bareAt around = True
            → HangsAt lexKind around.before False ((App head [argument, ..rest]).el around) :=
            around bare indent column =>
              let el :=
                appElHangs lexKind head argument rest around indent column
                  (rewrite firstWordLead (App head [argument, ..rest]) within then
                    leadLeading head.lead around around.at (leadOfLead head headLead) bare)
                  (inset seat =>
                    rewrite headTrails then
                      elUnheld lexKind
                        (head.el { around | hoisted = True })
                        inset
                        seat
                        around.before
                        False
                        wordStart
                        (leadHangsOf head headFacts { around | hoisted = True } byComputing inset seat))
                  (argsHang around.inArm head
                    (around.at + head.size)
                    [argument, ..rest]
                    headTrails
                    (Bool.andRight within)
                    (Bool.andRight lexical)
                    argumentsQuiet
                    keys)
              elQuiet lexKind _ indent column around.before _ wordStart el (lastQuiet argument rest argumentsQuiet)
          (hangs, level first around bare => hangs around bare)
    | Infix InfixBinary left operator right, within =>
      let word := fixedWord operator.text Comments.none
      let leftLead := Bool.andLeft lead
      let rightQuiet := Bool.andRight (Bool.andRight lead)
      let leftFacts := leadFacts left (Bool.andLeft within) (Bool.andLeft lexical) leftLead keys
      let rightFacts :=
        leadFacts right
          (Bool.andLeft (Bool.andRight within))
          (Bool.andRight (Bool.andRight lexical))
          (quietLead right rightQuiet)
          keys
      let listed := Bool.andRight (Bool.andRight within)
      let pair: ∀ (level: Option Nat) (first: Bool) (around: Around) => left.bareAt around = True
        → PairFacts lexKind level first left word right around False False :=
        level first around bare =>
          (
            leadLinksOf left leftFacts level first around bare,
            quietRun operator.text (around.next left.trails left.size) (around.next left.trails left.size).at listed,
            chainRightPlain level right (around.next False (left.size + 1)) (Bool.andLeft (Bool.andRight within)),
            leadLinksOf right rightFacts level False
              (around.next False (left.size + 1))
              (quietBare right (around.next False (left.size + 1)) rightQuiet)
          )
      let hangs: ∀ (around: Around) => (Infix InfixBinary left word right).bareAt around = True
        → HangsAt lexKind around.before False ((Infix InfixBinary left word right).el around) :=
        around bare indent column =>
          binaryChainHangs lexKind left word right around indent column False False
            (rewrite firstWordLead (Infix InfixBinary left word right) within then
              leadLeading left.lead around around.at (leadOfLead left leftLead) bare)
            (opensNoArms left (Infix InfixBinary left word right).chainLevel (Bool.andLeft within))
            (pair (Infix InfixBinary left word right).chainLevel True { around | hoisted = True } byComputing)
      rewrite quietIs operator (Bool.andLeft (Bool.andRight lead)) then
        (
          hangs,
          level first around bare =>
            match chained: (Infix InfixBinary left word right).inChain level with
              | True =>
                let (leftLinks, run, rightDocs, rightLinks) := pair level first around bare
                (False, leftLinks, run, rightDocs, rightLinks)
              | False => hangs around bare
        )
    | Infix InfixArrow left operator right, within =>
      let word := fixedWord operator.text Comments.none
      let leftLead := Bool.andLeft lead
      let rightQuiet := Bool.andRight (Bool.andRight lead)
      let leftFacts := leadFacts left (Bool.andLeft within) (Bool.andLeft lexical) leftLead keys
      let rightFacts :=
        leadFacts right
          (Bool.andLeft (Bool.andRight within))
          (Bool.andRight (Bool.andRight lexical))
          (quietLead right rightQuiet)
          keys
      let listed := Bool.andRight (Bool.andRight within)
      let pair: ∀ (level: Option Nat) (first: Bool) (around: Around) => left.bareAt around = True
        → PairFacts lexKind level first left word right around False False :=
        level first around bare =>
          (
            leadLinksOf left leftFacts level first around bare,
            quietRun operator.text (around.next left.trails left.size) (around.next left.trails left.size).at listed,
            chainRightPlain level right (around.next False (left.size + 1)) (Bool.andLeft (Bool.andRight within)),
            leadLinksOf right rightFacts level False
              (around.next False (left.size + 1))
              (quietBare right (around.next False (left.size + 1)) rightQuiet)
          )
      let hangs: ∀ (around: Around) => (Infix InfixArrow left word right).bareAt around = True
        → HangsAt lexKind around.before False ((Infix InfixArrow left word right).el around) :=
        around bare indent column =>
          arrowChainHangs lexKind left word right around indent column False False
            (rewrite firstWordLead (Infix InfixArrow left word right) within then
              leadLeading left.lead around around.at (leadOfLead left leftLead) bare)
            (opensNoArms left (Infix InfixArrow left word right).chainLevel (Bool.andLeft within))
            (pair (Infix InfixArrow left word right).chainLevel True { around | hoisted = True } byComputing)
      rewrite quietIs operator (Bool.andLeft (Bool.andRight lead)) then
        (
          hangs,
          level first around bare =>
            match chained: (Infix InfixArrow left word right).inChain level with
              | True =>
                let (leftLinks, run, rightDocs, rightLinks) := pair level first around bare
                (False, leftLinks, run, rightDocs, rightLinks)
              | False => hangs around bare
        )

--| Each quiet slice 1 expression hangs as an element wherever it stands, and as a chain's operand: `leadFacts`,
--| with no comments above its first token.
theorem exprFacts ∀ (expr: Expr)
    (within: expr.within1 = True)
    (lexical: expr.lexical1 = True)
    (quiet: expr.quiet1 = True) (keys: QuietKeys):
    ExprFacts expr :=
  let facts := leadFacts expr within lexical (quietLead expr quiet) keys
  (
    around => leadHangsOf expr facts around (quietBare expr around quiet),
    level first around => leadLinksOf expr facts level first around (quietBare expr around quiet)
  )
