--| Every theorem of Toy++ (toy-plus-plus.md §3), stated. The ones at the
--| top are open: each `?` is a stage's work (`../SKETCH-PLUS.md` says
--| which). The ones at the bottom (`tidy`'s four, `printParses`,
--| `format`'s three) are proved from them, so the statements fit
--| together.

namespace Toy.Plus.Proofs
import Toy.Plus (..)
import Toy.Doc.Proofs (Event)
import Toy.Fmt (FormatResult)
import Toy.Fmt.Proofs (Descending, Unspaced, Views, formattedInjective, viewOf, viewsOf)
import Toy.Syntax (Comment, Comments, Lexed, Operator, Spaced, Token, Trivia, lex)
import Std (Bool, Eq, List, Nat, NonEmptyList, Option, Parse, Result, Text)

-- What a pass and the printer may assume of a tree.

--| The toy's `Shaped`, for this tree: a field's target and a callee are
--| postfix, `-` stands before an operand, an operator's sides are grouped
--| by precedence. A list's last item needs no clause: no comma holds
--| comments.
def Shaped: Expr → Prop
  | Var _ _ => True
  | NumberLiteral _ _ => True
  | StringLiteral _ _ => True
  | Bracketed _ inner _ => Shaped inner
  | Field target _ _ _ => target.isPostfix = True ∧ Shaped target
  | Negate _ operand => operand.isOperand = True ∧ Shaped operand
  | Binary operator _ left right =>
    operator.level ≤ left.chainLevel
      ∧ operator.level < right.chainLevel
      ∧ left.isChain = True
      ∧ right.isChain = True
      ∧ Shaped left
      ∧ Shaped right
  | ListLiteral _ items _ _ => ShapedItems items
  | Call callee _ arguments _ _ => callee.isPostfix = True ∧ Shaped callee ∧ ShapedItems arguments
  | If _ condition _ whenTrue _ whenFalse => Shaped condition ∧ ShapedBody whenTrue ∧ ShapedBody whenFalse

def ShapedItems: List Expr → Prop
  | [] => True
  | [first, ..rest] => Shaped first ∧ ShapedItems rest

def ShapedBody: Body → Prop
  | { statements } => ShapedLines statements ∧ ClosedLines statements

--| There is a last line, and it is a statement, not a comment line.
def ClosedLines: List (Spaced Statement) → Prop
  | [] => False
  | [{ line = StatementNote _, .. }] => False
  | [_] => True
  | [_, ..rest] => ClosedLines rest

def ShapedLines: List (Spaced Statement) → Prop
  | [] => True
  | [{ line, .. }, ..rest] => ShapedStatement line ∧ ShapedLines rest

def ShapedStatement: Statement → Prop
  | Let _ _ _ _ body => ShapedBody body
  | Bare value => Shaped value
  | StatementNote _ => True

def ShapedDeclarations: List (Spaced Declaration) → Prop
  | [] => True
  | [{ line = Function _ _ _ _ _ _ _ _ _ body, .. }, ..rest] => ShapedBody body ∧ ShapedDeclarations rest
  | [{ line = Value _ _ _ _ body, .. }, ..rest] => ShapedBody body ∧ ShapedDeclarations rest
  | [_, ..rest] => ShapedDeclarations rest

def ShapedFile (file: SourceFile): Prop := ShapedDeclarations file.declarations

--| An expression of the parser's shape that may stand at `position`.
def ShapedAt (position: Position) (expr: Expr): Prop := expr.fits position.slot = True ∧ Shaped expr

--| A body that is one expression.
def OneExpression: List (Spaced Statement) → Prop
  | [{ line = Bare _, .. }] => True
  | _ => False

--| The toy's `HeadedExpr`, for this tree: outside brackets no statement's
--| first token has comments above it; inside brackets every body is one
--| expression; no body keeps a blank line above its first line.
def HeadedExpr (bracketed: Bool): Expr → Prop
  | Var _ _ => True
  | NumberLiteral _ _ => True
  | StringLiteral _ _ => True
  | Bracketed _ inner _ => HeadedExpr True inner
  | ListLiteral _ items _ _ => HeadedItems items
  | Call callee _ arguments _ _ => HeadedExpr bracketed callee ∧ HeadedItems arguments
  | Field target _ _ _ => HeadedExpr bracketed target
  | Negate _ operand => HeadedExpr bracketed operand
  | Binary _ _ left right => HeadedExpr bracketed left ∧ HeadedExpr bracketed right
  | If _ condition _ whenTrue _ whenFalse =>
    HeadedExpr bracketed condition ∧ HeadedBody bracketed whenTrue ∧ HeadedBody bracketed whenFalse

def HeadedItems: List Expr → Prop
  | [] => True
  | [first, ..rest] => HeadedExpr True first ∧ HeadedItems rest

def HeadedBody (bracketed: Bool): Body → Prop
  | { statements } =>
    HeadedLines bracketed statements ∧ Unspaced statements ∧ (bracketed = True → OneExpression statements)

def HeadedLines (bracketed: Bool): List (Spaced Statement) → Prop
  | [] => True
  | [{ line, .. }, ..rest] => HeadedStatement bracketed line ∧ HeadedLines bracketed rest

def HeadedStatement (bracketed: Bool): Statement → Prop
  | Let letComments _ _ _ body => letComments.above = [] ∧ HeadedBody False body
  | Bare value => (bracketed = False → value.firstAbove = []) ∧ HeadedExpr bracketed value
  | StatementNote _ => True

def HeadedDeclarations: List (Spaced Declaration) → Prop
  | [] => True
  | [{ line = Function fnComments _ _ _ _ _ _ _ _ body, .. }, ..rest] =>
    fnComments.above = [] ∧ HeadedBody False body ∧ HeadedDeclarations rest
  | [{ line = Value letComments _ _ _ body, .. }, ..rest] =>
    letComments.above = [] ∧ HeadedBody False body ∧ HeadedDeclarations rest
  | [_, ..rest] => HeadedDeclarations rest

def HeadedFile (file: SourceFile): Prop := HeadedDeclarations file.declarations ∧ Unspaced file.declarations

--| Rule N's guarantee, as the printer needs it: every closer that has a
--| trailing comment may keep it (`settledCloser`), so the printed comment
--| is read back onto the same closer.
def Settled: Expr → Prop
  | Var _ _ => True
  | NumberLiteral _ _ => True
  | StringLiteral _ _ => True
  | Bracketed _ inner close => Settled inner ∧ settledCloser inner.endsWithComment close = True
  | ListLiteral open items trailingComma close =>
    SettledItems items ∧ settledCloser (not trailingComma && lastEndsWithComment open items) close = True
  | Call callee open arguments trailingComma close =>
    Settled callee
      ∧ SettledItems arguments
      ∧ settledCloser (not trailingComma && lastEndsWithComment open arguments) close = True
  | Field target _ _ _ => Settled target
  | Negate _ operand => Settled operand
  | Binary _ _ left right => Settled left ∧ Settled right
  | If _ condition _ whenTrue _ whenFalse => Settled condition ∧ SettledBody whenTrue ∧ SettledBody whenFalse

def SettledItems: List Expr → Prop
  | [] => True
  | [first, ..rest] => Settled first ∧ SettledItems rest

def SettledBody: Body → Prop
  | { statements } => SettledLines statements

def SettledLines: List (Spaced Statement) → Prop
  | [] => True
  | [{ line, .. }, ..rest] => SettledStatement line ∧ SettledLines rest

def SettledStatement: Statement → Prop
  | Let _ _ _ _ body => SettledBody body
  | Bare value => Settled value
  | StatementNote _ => True

def SettledType: TypeExpr → Prop
  | TypeName _ _ => True
  | TypeBracketed _ inner close => SettledType inner ∧ settledCloser inner.endsWithComment close = True

def SettledGroups: List ParameterGroup → Prop
  | [] => True
  | [Typed _ _ annotation, ..rest] => SettledType annotation ∧ SettledGroups rest
  | [_, ..rest] => SettledGroups rest

def SettledDeclarations: List (Spaced Declaration) → Prop
  | [] => True
  | [{ line = Function _ _ _ _ open groups trailingComma close _ body, .. }, ..rest] =>
    SettledGroups groups
      ∧ settledCloser (not trailingComma && groupsEndWithComment open groups) close = True
      ∧ SettledBody body
      ∧ SettledDeclarations rest
  | [{ line = Value _ _ _ _ body, .. }, ..rest] => SettledBody body ∧ SettledDeclarations rest
  | [_, ..rest] => SettledDeclarations rest

def SettledFile (file: SourceFile): Prop := SettledDeclarations file.declarations

--| The toy's `LexicalFile`, for this tree: every name, number, string
--| and comment in the tree is one the lexer could have given.
def LexicalFile (file: SourceFile): Prop := ?

def Lexical (expr: Expr): Prop := ?

--| What a pass and the printer may assume of a tree, and must keep.
def Parsed (file: SourceFile): Prop := ShapedFile file ∧ LexicalFile file ∧ HeadedFile file ∧ SettledFile file

-- Layer N: rule N on tokens.

--| Every comment the tokens and the end of the file hold, in order.
def commentsOf (tokens: List (Parse.Located Token)) (endTrivia: List Trivia): List Comment :=
  tokens.flatMap (token => ownLines token.value.above ++ (token.value.trailing.map (comment => comment.value)).toList)
    ++ ownLines endTrivia

def ownLines (trivia: List Trivia): List Comment := trivia.filterMap (match some | OwnLine comment => comment)

--| Rule N loses no comment and keeps their order.
--|
--| Proof idea: a comment moves back only past tokens that hold none, and
--| a comma's go to the front of the next token's.
theorem settledKeepsComments ∀ (lexed: Lexed):
    commentsOf lexed.settled.tokens lexed.settled.endTrivia = commentsOf lexed.tokens lexed.endTrivia :=
  ?

--| Rule N changes nothing the second time.
theorem settledIdempotent ∀ (lexed: Lexed): lexed.settled.settled = lexed.settled := ?

--| After rule N, the tokens are the same tokens at the same places: only
--| comments moved.
theorem settledOffsets ∀ (lexed: Lexed):
    lexed.settled.tokens.map (token => token.offset) = lexed.tokens.map (token => token.offset) :=
  ?

--| The trace of the printing rules over this tree: the toy's
--| `FileEvents`, with a comment after a closer's event where `Closing`
--| writes it.
def FileEvents (file: SourceFile) (events: List Event): Prop := ?

--| The printed text, lexed and settled, has the views of the tree's own
--| events: rule N puts each printed comment back on the token the tree
--| holds it on, whichever closers the engine wrote before it.
theorem settledViews ∀ (file: SourceFile) (width: Nat)
    (parsed: Parsed file)
    (bare: file.withoutTrailingCommas = file):
    ∃ (events: List Event) (lexed: Lexed) (tokens: List (Parse.Located Token)) (endTrivia: List Trivia) => FileEvents
        file events
      ∧ lex (file.print width) = Ok lexed
      ∧ lexed.settled.tokens = tokens.reverse
      ∧ lexed.settled.endTrivia = endTrivia.reverse
      ∧ tokens.map viewOf = (viewsOf events).views
      ∧ endTrivia = (viewsOf events).pending
      ∧ Descending (tokens.map (token => token.offset)) :=
  ?

-- Route (A): `Settled` by construction.

theorem receiveSettled ∀ (expr: Expr) (comment: Comment)
    (settled: Settled expr)
    (open: expr.endsWithComment = False):
    Settled (expr.receive comment) :=
  ?

theorem closedSettled ∀ (open: Comments) (inner: Expr) (close: Comments)
    (settled: Settled inner):
    Settled (closed open inner close) :=
  ?

--| On a settled tree `closed` is `Bracketed`: what the read-back needs
--| where the parser builds a closer.
theorem closedSame ∀ (open: Comments) (inner: Expr) (close: Comments)
    (settled: settledCloser inner.endsWithComment close = True):
    closed open inner close = Bracketed open inner close :=
  ?

theorem closedListSettled ∀ (open: Comments) (items: List Expr) (trailingComma: Bool) (close: Comments)
    (settled: SettledItems items):
    match closedList open items trailingComma close with
      | (settledOpen, settledItems, settledClose) =>
        SettledItems settledItems
          ∧ settledCloser (not trailingComma && lastEndsWithComment settledOpen settledItems) settledClose = True :=
  ?

theorem closedListSame ∀ (open: Comments) (items: List Expr) (trailingComma: Bool) (close: Comments)
    (settled: settledCloser (not trailingComma && lastEndsWithComment open items) close = True):
    closedList open items trailingComma close = (open, items, close) :=
  ?

-- The walk: what the parser guarantees.

theorem parseParsed ∀ (source: Text) (file: SourceFile) (parsed: parse source = Ok file): Parsed file := ?

-- The shared traversal (§3.4): each fact once for every `step`.

--| A step that keeps each expression's plain form keeps the whole's.
theorem walkKeepsPlain ∀ (step: Position → Expr → Expr)
    (keeps: ∀ (position: Position) (expr: Expr) => (step position expr).plain = expr.plain)
    (position: Position) (expr: Expr):
    (expr.walk step position).plain = expr.plain :=
  ?

--| A step that keeps the parser's shape where it stands keeps it
--| everywhere.
theorem walkKeepsShaped ∀ (step: Position → Expr → Expr)
    (keeps: ∀ (position: Position) (expr: Expr) => ShapedAt position expr → ShapedAt position (step position expr))
    (position: Position) (expr: Expr)
    (shaped: ShapedAt position expr):
    ShapedAt position (expr.walk step position) :=
  ?

theorem walkKeepsHeaded ∀ (step: Position → Expr → Expr)
    (keeps: ∀ (position: Position) (expr: Expr) => HeadedExpr position.bracketed expr
      → HeadedExpr position.bracketed (step position expr))
    (keepsFirst: ∀ (position: Position) (expr: Expr) => expr.firstAbove = [] → (step position expr).firstAbove = [])
    (position: Position) (expr: Expr)
    (headed: HeadedExpr position.bracketed expr):
    HeadedExpr position.bracketed (expr.walk step position) :=
  ?

theorem walkKeepsSettled ∀ (step: Position → Expr → Expr)
    (keeps: ∀ (position: Position) (expr: Expr) => Settled expr → Settled (step position expr))
    (keepsEnd: ∀ (position: Position) (expr: Expr) => expr.endsWithComment = True
      → (step position expr).endsWithComment = True)
    (position: Position) (expr: Expr)
    (settled: Settled expr):
    Settled (expr.walk step position) :=
  ?

theorem walkKeepsLexical ∀ (step: Position → Expr → Expr)
    (keeps: ∀ (position: Position) (expr: Expr) => Lexical expr → Lexical (step position expr))
    (position: Position) (expr: Expr)
    (lexical: Lexical expr):
    Lexical (expr.walk step position) :=
  ?

--| A step whose result needs no second walk, once what is inside it is
--| walked, makes a walk that finishes in one run.
theorem walkIdempotent ∀ (step: Position → Expr → Expr)
    (settles: ∀ (position: Position) (expr: Expr) => expr.walkInside step position.bracketed = expr
      → (step position expr).walk step position = step position expr)
    (position: Position) (expr: Expr):
    (expr.walk step position).walk step position = expr.walk step position :=
  ?

-- P1, `takes`.

theorem takesKeepMeaning ∀ (file: SourceFile): file.withTakes.meaning = file.meaning := ?

theorem takesIdempotent ∀ (file: SourceFile): file.withTakes.withTakes = file.withTakes := ?

theorem takesKeepParsed ∀ (file: SourceFile) (parsed: Parsed file): Parsed file.withTakes := ?

-- P2, trailing commas.

theorem commasKeepMeaning ∀ (file: SourceFile): file.withoutTrailingCommas.meaning = file.meaning := ?

theorem commasIdempotent ∀ (file: SourceFile):
    file.withoutTrailingCommas.withoutTrailingCommas = file.withoutTrailingCommas :=
  ?

theorem commasKeepParsed ∀ (file: SourceFile) (parsed: Parsed file): Parsed file.withoutTrailingCommas := ?

theorem commasKeepTakes ∀ (file: SourceFile)
    (tidy: file.withTakes = file):
    file.withoutTrailingCommas.withTakes = file.withoutTrailingCommas :=
  ?

-- P3, spare brackets.

theorem dropPairPlain ∀ (position: Position) (expr: Expr): (dropPair position expr).plain = expr.plain := ?

--| The precedence argument: the content of a dropped pair may stand
--| where the pair stood, because `dropPair` asked.
theorem dropPairShaped ∀ (position: Position) (expr: Expr)
    (shaped: ShapedAt position expr):
    ShapedAt position (dropPair position expr) :=
  ?

--| What was read inside brackets and `standsOutside` could have been
--| read outside them.
theorem standsOutsideHeaded ∀ (expr: Expr)
    (headed: HeadedExpr True expr)
    (stands: expr.standsOutside = True):
    HeadedExpr False expr :=
  ?

theorem dropPairHeaded ∀ (position: Position) (expr: Expr)
    (headed: HeadedExpr position.bracketed expr):
    HeadedExpr position.bracketed (dropPair position expr) :=
  ?

theorem dropPairSettled ∀ (position: Position) (expr: Expr) (settled: Settled expr): Settled (dropPair position expr) :=
  ?

--| A pair kept inside brackets is kept outside them, where `dropPair`
--| asks more: why the content of a dropped pair needs no second walk.
theorem dropPairSettles ∀ (position: Position) (expr: Expr)
    (inside: expr.walkInside dropPair position.bracketed = expr):
    (dropPair position expr).walk dropPair position = dropPair position expr :=
  ?

theorem bracketsKeepMeaning ∀ (file: SourceFile): file.withoutSpareBrackets.meaning = file.meaning := ?

theorem bracketsIdempotent ∀ (file: SourceFile):
    file.withoutSpareBrackets.withoutSpareBrackets = file.withoutSpareBrackets :=
  ?

theorem bracketsKeepParsed ∀ (file: SourceFile) (parsed: Parsed file): Parsed file.withoutSpareBrackets := ?

theorem bracketsKeepTakes ∀ (file: SourceFile)
    (tidy: file.withTakes = file):
    file.withoutSpareBrackets.withTakes = file.withoutSpareBrackets :=
  ?

theorem bracketsKeepCommas ∀ (file: SourceFile)
    (tidy: file.withoutTrailingCommas = file):
    file.withoutSpareBrackets.withoutTrailingCommas = file.withoutSpareBrackets :=
  ?

-- P4, merging.

theorem plainBare ∀ (annotation: TypeExpr): annotation.plain.bare = annotation.bare := ?

--| Merging a group into the groups after it splits to the same names
--| and types.
theorem mergeIntoPlain ∀ (group: ParameterGroup) (merged: List ParameterGroup):
    plainGroups (mergeInto group merged) = group.plain ++ plainGroups merged :=
  ?

theorem mergeGroupsIdempotent ∀ (groups: List ParameterGroup): mergeGroups (mergeGroups groups) = mergeGroups groups :=
  ?

theorem mergeKeepsMeaning ∀ (file: SourceFile): file.withMergedParameters.meaning = file.meaning := ?

theorem mergeIdempotent ∀ (file: SourceFile):
    file.withMergedParameters.withMergedParameters = file.withMergedParameters :=
  ?

theorem mergeKeepsParsed ∀ (file: SourceFile) (parsed: Parsed file): Parsed file.withMergedParameters := ?

theorem mergeKeepsTakes ∀ (file: SourceFile)
    (tidy: file.withTakes = file):
    file.withMergedParameters.withTakes = file.withMergedParameters :=
  ?

theorem mergeKeepsCommas ∀ (file: SourceFile)
    (tidy: file.withoutTrailingCommas = file):
    file.withMergedParameters.withoutTrailingCommas = file.withMergedParameters :=
  ?

theorem mergeKeepsBrackets ∀ (file: SourceFile)
    (tidy: file.withoutSpareBrackets = file):
    file.withMergedParameters.withoutSpareBrackets = file.withMergedParameters :=
  ?

-- The printer.

--| The parser reads back tokens whose views are those of the tree's
--| events: the toy's `spellsFile` then `runsFileSpelled`, for this tree.
theorem readsBack ∀ (file: SourceFile) (events: List Event)
    (tokens: List (Parse.Located Token)) (endTrivia: List Trivia)
    (parsed: Parsed file)
    (bare: file.withoutTrailingCommas = file)
    (laid: FileEvents file events)
    (views: tokens.map viewOf = (viewsOf events).views)
    (pending: endTrivia = (viewsOf events).pending)
    (offsets: Descending (tokens.map (token => token.offset))):
    Parse.Runs (() => sourceFile endTrivia.reverse) tokens.reverse [] file :=
  ?

-- Proved from the statements above.

theorem parseReads ∀ (source: Text) (lexed: Lexed) (file: SourceFile)
    (lexes: lex source = Ok lexed)
    (runs: Parse.Runs (() => sourceFile lexed.settled.endTrivia) lexed.settled.tokens [] file):
    parse source = Ok file :=
  let whole := Parse.runsWhole lexed.settled.tokens (() => sourceFile lexed.settled.endTrivia) file runs
  rewrite lexes, whole then byComputing

--| The toy's theorem, for a tree and not for a source: a tree with the
--| parser's guarantees and no trailing comma, printed at any width,
--| parses to itself.
theorem printParses ∀ (file: SourceFile) (width: Nat)
    (parsed: Parsed file)
    (bare: file.withoutTrailingCommas = file):
    parse (file.print width) = Ok file :=
  match settledViews file width parsed bare with
    | (events, lexed, tokens, endTrivia, laid, lexes, sameTokens, sameEnd, views, pending, offsets) =>
      parseReads
        (file.print width)
        lexed
        file
        lexes
        (rewrite sameTokens, sameEnd then readsBack file events tokens endTrivia parsed bare laid views pending offsets)

theorem tidyKeepsMeaning ∀ (file: SourceFile): file.tidy.meaning = file.meaning := calc file.tidy.meaning
  _ = file.withTakes.withoutTrailingCommas.withoutSpareBrackets.meaning :=
    mergeKeepsMeaning file.withTakes.withoutTrailingCommas.withoutSpareBrackets
  _ = file.withTakes.withoutTrailingCommas.meaning := bracketsKeepMeaning file.withTakes.withoutTrailingCommas
  _ = file.withTakes.meaning := commasKeepMeaning file.withTakes
  _ = file.meaning := takesKeepMeaning file

theorem tidyParsed ∀ (file: SourceFile) (parsed: Parsed file): Parsed file.tidy :=
  mergeKeepsParsed file.withTakes.withoutTrailingCommas.withoutSpareBrackets
    (bracketsKeepParsed file.withTakes.withoutTrailingCommas
      (commasKeepParsed file.withTakes (takesKeepParsed file parsed)))

--| A tidied tree has no trailing comma: what `printParses` asks.
theorem tidyBare ∀ (file: SourceFile): file.tidy.withoutTrailingCommas = file.tidy :=
  mergeKeepsCommas file.withTakes.withoutTrailingCommas.withoutSpareBrackets
    (bracketsKeepCommas file.withTakes.withoutTrailingCommas (commasIdempotent file.withTakes))

theorem tidyTakes ∀ (file: SourceFile): file.tidy.withTakes = file.tidy :=
  mergeKeepsTakes file.withTakes.withoutTrailingCommas.withoutSpareBrackets
    (bracketsKeepTakes file.withTakes.withoutTrailingCommas (commasKeepTakes file.withTakes (takesIdempotent file)))

theorem tidyBrackets ∀ (file: SourceFile): file.tidy.withoutSpareBrackets = file.tidy :=
  mergeKeepsBrackets file.withTakes.withoutTrailingCommas.withoutSpareBrackets
    (bracketsIdempotent file.withTakes.withoutTrailingCommas)

--| Each pass leaves a tidied tree alone, so all four do.
theorem tidyIdempotent ∀ (file: SourceFile): file.tidy.tidy = file.tidy := calc file.tidy.tidy
  _ = file.tidy.withoutTrailingCommas.withoutSpareBrackets.withMergedParameters :=
    Eq.cong
      ((tree: SourceFile) => tree.withoutTrailingCommas.withoutSpareBrackets.withMergedParameters)
      (tidyTakes file)
  _ = file.tidy.withoutSpareBrackets.withMergedParameters :=
    Eq.cong ((tree: SourceFile) => tree.withoutSpareBrackets.withMergedParameters) (tidyBare file)
  _ = file.tidy.withMergedParameters := Eq.cong ((tree: SourceFile) => tree.withMergedParameters) (tidyBrackets file)
  _ = file.tidy := mergeIdempotent file.withTakes.withoutTrailingCommas.withoutSpareBrackets

theorem formatAnswers ∀ (source: Text) (width: Nat) (tree: SourceFile)
    (parsed: parse source = Ok tree):
    format source width = Formatted (tree.tidy.print width) :=
  rewrite parsed then byComputing

--| The output is the source's tree, tidied and printed, and parses to
--| that tidied tree.
theorem formatRoundTrip ∀ (source: Text) (width: Nat) (output: Text)
    (h: format source width = Formatted output):
    ∃ (tree: SourceFile) => parse source = Ok tree ∧ output = tree.tidy.print width ∧ parse output = Ok tree.tidy :=
  match e: parse source with
    | Ok tree =>
      let same := formattedInjective (tree.tidy.print width) output h
      (
        tree,
        byComputing,
        same.flipped,
        (rewrite <- same then printParses tree.tidy width (tidyParsed tree (parseParsed source tree e)) (tidyBare tree))
      )

--| Formatting keeps the program: the output parses, and means what the
--| source means.
theorem formatKeepsMeaning ∀ (source: Text) (width: Nat) (output: Text)
    (h: format source width = Formatted output):
    ∃ (before after: SourceFile) => parse source = Ok before
      ∧ parse output = Ok after
      ∧ after.meaning = before.meaning :=
  match formatRoundTrip source width output h with
    | (tree, parsed, same, reparsed) => (tree, tree.tidy, parsed, reparsed, tidyKeepsMeaning tree)

--| Formatting the output again, at the same width, gives the output.
theorem formatIdempotent ∀ (source: Text) (width: Nat) (output: Text)
    (h: format source width = Formatted output):
    format output width = Formatted output :=
  match formatRoundTrip source width output h with
    | (tree, parsed, same, reparsed) =>
      rewrite same then
        Eq.trans
          (formatAnswers (tree.tidy.print width) width tree.tidy (rewrite <- same then reparsed))
          (Eq.cong ((tidied: SourceFile) => Formatted (tidied.print width)) (tidyIdempotent tree))
