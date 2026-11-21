--| Facts about quiet slice 1 expressions (`Expr.quiet`, and `Expr.leadQuiet` for those quiet but for own-line comments
--| above their first token): their tokens' spellings and operators' facts.

namespace Fmt.ExprHangProofs
import Std (Bool, DecEq, Doc, Eq, List, Nat, Option, Text, Void)
import Std.Doc (..)
import Std.Doc.Proofs (..)
import Syntax (Comments, Expr, InfixKind, Note, Tok, Word)
import Fmt (..)
import Fmt.OperatorList (operators1, operatorListed)
import Fmt.HangProofs (..)
import Fmt.MarkProofs (allKeysFrom, keysFrom)
import Fmt.AppHangProofs (ArgsHang, HangsFor, appElHangs, argAround, lastArg)
import Fmt.ChainHangProofs (GluesAt, HangsAt, PairFacts, arrowChainHangs, arrowLeafGlues, binaryChainHangs)
import Fmt.BracketHangProofs (ItemsHang, groupedBracketHangs, lastTrails, listHangs, tupleHangs)
import Fmt.DeclHangProofs (WordToken)
import Fmt.SpellProofs (..)
import Fmt.TreeJoinProofs (
  arrowListed,
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
def Word.quiet (word: Word): Bool := match word.comments with
  | { above = [], after = None, blankBefore = False } => True
  | _ => False

--| An expression whose every token is quiet, and whose calls each have an argument, as every call the parser reads
--| does.
def Expr.quiet: Expr → Bool
  | Atom _ word => word.quiet
  | Paren open inner close => open.quiet && inner.quiet && close.quiet
  | Tuple open items _ close | ListOf open items _ close => open.quiet && allQuiet items && close.quiet
  | App head arguments => !arguments.isEmpty && head.quiet && allQuiet arguments
  | Infix _ left operator right => left.quiet && operator.quiet && right.quiet
  | Prefix operator operand => operator.quiet && operand.quiet
  | _ => False

def allQuiet: List Expr → Bool
  | [] => True
  | [expr, ..rest] => expr.quiet && allQuiet rest

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

theorem plainOperator ∀ [text: Text]
    (plain: plainKind (lexKind text) = True)
    (word: wordText text = True):
    OperatorFacts text :=
  (Inl (plainOf (lexKind text) plain), wordTokenOf text word)

theorem arrowOperator ∀ (text: Text) (arrow: lexKind text = Arrow) (word: wordText text = True): OperatorFacts text :=
  (Inr arrow, wordTokenOf text word)

def operatorsFacts: List.All OperatorFacts operators1 := (
  arrowOperator _ byComputing byComputing,
  arrowOperator _ byComputing byComputing,
  plainOperator byComputing byComputing,
  plainOperator byComputing byComputing,
  plainOperator byComputing byComputing,
  plainOperator byComputing byComputing,
  plainOperator byComputing byComputing,
  plainOperator byComputing byComputing,
  plainOperator byComputing byComputing,
  plainOperator byComputing byComputing,
  plainOperator byComputing byComputing,
  plainOperator byComputing byComputing,
  plainOperator byComputing byComputing,
  plainOperator byComputing byComputing,
  plainOperator byComputing byComputing,
  plainOperator byComputing byComputing,
  plainOperator byComputing byComputing,
  plainOperator byComputing byComputing,
  plainOperator byComputing byComputing,
  plainOperator byComputing byComputing,
  plainOperator byComputing byComputing,
  plainOperator byComputing byComputing,
  Trivial
)

theorem operatorFacts ∀ (text: Text) (listed: operatorText1 text = True): OperatorFacts text :=
  List.allMem OperatorFacts text operators1 operatorsFacts (operatorListed text listed)

-- Shapes `within1` fixes.

--| A slice 1 expression in a paren is written as it is.
theorem parenInnerPlain ∀ (inner: Expr) (innerAround: Around)
    (within: inner.within1 = True):
    parenInner inner innerAround = inner.el innerAround :=
  match inner, within with
    | Atom _ _ |
        Paren _ _ _ |
        Tuple _ _ _ _ |
        ListOf _ _ _ _ |
        App _ _ |
        Infix InfixBinary _ _ _ |
        Infix InfixArrow _ _ _ |
        Prefix _ _, _ => byComputing

--| A slice 1 operand after a chain's operator is a space and its links.
theorem chainRightPlain ∀ (level: Option Nat) (right: Expr) (rightAround: Around)
    (within: right.within1 = True):
    chainRight level right rightAround = [Doc.text " ", ..linkDocs level False right rightAround] :=
  match right, within with
    | Atom _ _ |
        Paren _ _ _ |
        Tuple _ _ _ _ |
        ListOf _ _ _ _ |
        App _ _ |
        Infix InfixBinary _ _ _ |
        Infix InfixArrow _ _ _ |
        Prefix _ _, _ => byComputing

--| A slice 1 chain opens no arms: it has no `match`.
theorem opensNoArms ∀ (expr: Expr) (level: Option Nat) (within: expr.within1 = True): expr.opensArms level = False :=
  match expr, within with
    | Atom _ _ | Paren _ _ _ | Tuple _ _ _ _ | ListOf _ _ _ _ | App _ _, _ => byComputing
    | Infix InfixBinary left operator right, within =>
      rewrite opensNoArms left level (Bool.andLeft within),
          Bool.andFalse ((Infix InfixBinary left operator right).inChain level)
    | Infix InfixArrow left operator right, within =>
      rewrite opensNoArms left level (Bool.andLeft within),
          Bool.andFalse ((Infix InfixArrow left operator right).inChain level)
    | Prefix _ _, _ => byComputing

-- Comments above the first token.

--| A token with no comment after it and no blank line kept above it; it may have own-line comments above it.
def Word.lead (word: Word): Bool := match word.comments with
  | { above = _, after = None, blankBefore = False } => True
  | _ => False

--| An expression quiet but for own-line comments above its first token (`Expr.lead`), as a declaration's type or
--| value may have them.
def Expr.leadQuiet: Expr → Bool
  | Atom _ word => word.lead
  | Paren open inner close => open.lead && inner.quiet && close.quiet
  | Tuple open items _ close | ListOf open items _ close => open.lead && allQuiet items && close.quiet
  | App head arguments => !arguments.isEmpty && head.leadQuiet && allQuiet arguments
  | Infix _ left operator right => left.leadQuiet && operator.quiet && right.quiet
  | Prefix operator operand => operator.lead && operand.quiet
  | _ => False

-- Brackets' marks.

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

-- The induction.

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

--| A slice 1 paren as a call's last argument is written as it is, with no hug.
theorem parenLast ∀ (open: Word) (inner: Expr) (close: Word) (around: Around)
    (within: inner.within1 = True):
    lastArgument (Paren open inner close) around = ((Paren open inner close).el around, None) :=
  match inner, within with
    | Atom _ _ |
        Paren _ _ _ |
        Tuple _ _ _ _ |
        ListOf _ _ _ _ |
        App _ _ |
        Infix InfixBinary _ _ _ |
        Infix InfixArrow _ _ _ |
        Prefix _ _, _ => byComputing
