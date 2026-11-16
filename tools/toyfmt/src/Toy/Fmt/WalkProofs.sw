--| What the parser guarantees of every tree it gives, proved in one walk
--| over its functions: each lemma follows one parser function with std's
--| `Parse.Gives` lemmas, one `Parse.givesThen` per step, and proves at its
--| leaves the three properties the printer's theorems need of a parsed
--| tree at once (`ParsedExpr` and the like):
--|
--| - `Shaped` (ShapeProofs.sw): operators grouped by precedence and
--|   chaining from the left, a call's callee and a field's target postfix,
--|   `-` before an operand; every body ends in a statement; no last
--|   parameter or item keeps a comma's comments;
--| - `Lexical` (ParsedProofs.sw): names, numbers, strings and comments are
--|   the lexer's tokens' texts, given tokens that are `Good`;
--| - `Headed` (HeadProofs.sw): no first token outside brackets holds
--|   comments above it in the tree, and no body keeps a blank line above
--|   its first line.
--|
--| The walk runs under `Parse.Invariant.every Good` (`GoodTokens`), which
--| `Lexical` needs and the other two ignore. A function that looks at the
--| next token is proved from each mark (`Parse.readsPeek`,
--| `Parse.readsWithMark`), so no lemma takes the handler's state apart.

namespace Toy.Fmt.Proofs
import Toy.Doc (..)
import Toy.Doc.Proofs (..)
import Toy.Syntax (..)
import Toy.Syntax.Proofs (..)
import Toy.Fmt (..)
import Std.Parse.Associativity (LeftAssociative)
import Std (And, Bool, Empty, Eq, List, NonEmptyList, Option, Pair, Parse, Result, Text, Void)

--| Tokens with the lexer's texts: what the walk assumes of the input left.
def GoodTokens: Parse.Invariant (Parse.Located Token) := Parse.Invariant.every Good

-- What each parser function gives.

--| An expression read at `layout`: of the parser's shape, with the
--| lexer's texts, and headed as an expression read there is.
def ParsedExpr (layout: Layout) (expr: Expr): Prop := Shaped expr ∧ Lexical expr ∧ HeadedAt layout expr

--| What `atom` and `suffixesFrom` give at `layout`: a postfix expression.
def ParsedPostfix (layout: Layout) (expr: Expr): Prop := PostfixShaped expr ∧ Lexical expr ∧ HeadedAt layout expr

--| What `negationsFrom` gives at `layout`: an operand.
def ParsedOperand (layout: Layout) (expr: Expr): Prop := OperandShaped expr ∧ Lexical expr ∧ HeadedAt layout expr

--| An item and whether a comma followed it.
def ParsedItem (read: (Item, Bool)): Prop := ShapedItem read ∧ LexicalItem read.fst ∧ HeadedItem read

def ParsedList (items: List Item): Prop := ShapedList items ∧ LexicalItems items ∧ HeadedItems items

--| Items and the closing bracket's comments.
def ParsedItems (found: (List Item, Comments)): Prop := ParsedList found.fst ∧ Fine found.snd

--| What `bareStatement` gives at `layout`.
def ParsedBare (layout: Layout) (line: Statement): Prop :=
  CodedShaped line ∧ CodedLexical line ∧ BareHeaded (bracketedOf layout) line

--| A statement read at its own start, outside brackets.
def ParsedLine (line: Statement): Prop := CodedShaped line ∧ CodedLexical line ∧ HeadedStatement False line

--| A statement's lines, the notes above it and itself.
def ParsedLines (lines: List (Spaced Statement)): Prop :=
  ClosedShaped lines ∧ ClosedLexical lines ∧ HeadedLines False lines

def ParsedBody (layout: Layout) (found: Body): Prop := ShapedBody found ∧ LexicalBody found ∧ HeadedBodyAt layout found

--| A block's body: outside brackets.
def ParsedBlock (found: Body): Prop := ShapedBody found ∧ LexicalBody found ∧ HeadedBody False found

def ParsedParameters (parameters: List Parameter): Prop := BareLast parameters ∧ LexicalParameters parameters

def ParsedDeclaration (line: Declaration): Prop :=
  ShapedDeclaration line ∧ LexicalDeclaration line ∧ HeadedDeclaration line

def ParsedDeclarations (lines: List (Spaced Declaration)): Prop :=
  ShapedDeclarations lines ∧ LexicalDeclarations lines ∧ HeadedDeclarations lines

--| What the parser guarantees of a file: `ShapedFile`, `LexicalFile` and
--| `HeadedFile`.
def Parsed (file: SourceFile): Prop := ShapedFile file ∧ LexicalFile file ∧ HeadedFile file

-- Tokens.

theorem givesSkip: Parse.Gives GoodTokens (() => skip()) (skipped => True) :=
  Parse.givesThen
    [first := found => True]
    (Parse.readsWeaken (Parse.readsNext (token => True)) (read found facts => byComputing))
    (skipped done => Parse.givesDone byComputing)

--| A note, then a value.
theorem givesNoted ∀ (problem: Parse.Problem) [x: a] [holds: a → Prop] (proved: holds x):
    Parse.Gives GoodTokens
      (() =>
        Parse.note problem
        x)
      holds :=
  Parse.givesThen (Parse.givesNote problem) (noted none => Parse.givesDone proved)

theorem givesSign ∀ (layout: Layout) (what: Text) (wanted: Punctuation):
    Parse.Gives GoodTokens (() => sign layout what wanted) Fine :=
  Parse.readsWeaken (Parse.readsOneEvery what (selectComments layout (signIs wanted))) (taken value found =>
    match found with
      | (token, single, good, selected) =>
        rewrite selectedComments layout (signIs wanted) token value selected then fineComments layout token good)

theorem givesKeyword ∀ (layout: Layout) (wanted: Keyword): Parse.Gives GoodTokens (() => keyword layout wanted) Fine :=
  Parse.readsWeaken
    (Parse.readsOneEvery "'${wanted.spelling}'" (selectComments layout (keywordIs wanted)))
    (taken value found =>
      match found with
        | (token, single, good, selected) =>
          rewrite selectedComments layout (keywordIs wanted) token value selected then fineComments layout token good)

theorem givesName ∀ (layout: Layout): Parse.Gives GoodTokens (() => name layout) FineNamed :=
  Parse.readsWeaken (Parse.readsOneEvery "a name" (selectWithComments layout nameOf)) (taken value found =>
    match found with
      | (token, single, good, selected) =>
        selectedName layout token value good.left (fineComments layout token good) selected)

theorem givesSignInBrackets ∀ (what: Text) (wanted: Punctuation):
    Parse.Gives GoodTokens (() => signInBrackets what wanted) (Parse.Perhaps Fine) :=
  Parse.readsPeek _ _ (start fine =>
    match e: start.rest with
      | [] => givesNoted (Parse.Problem.Expected what) [x := None] [holds := Parse.Perhaps Fine] byComputing
      | [token, ..later] =>
        match isSign: (signIs wanted token.value.kind).isSome with
          | False => givesNoted (Parse.Problem.Expected what) [x := None] [holds := Parse.Perhaps Fine] byComputing
          | True =>
            Parse.givesThen givesSkip (skipped done => Parse.givesDone (fineComments InBrackets token fine.holds.left)))

-- Items.

theorem givesItem ∀ (self: Layout → {Parse (Parse.Located Token)} Expr)
    (nested: ∀ (inner: Layout) => Parse.Gives GoodTokens (() => self inner) (ParsedExpr inner)):
    Parse.Gives GoodTokens (() => item self) ParsedItem :=
  Parse.givesThen (nested InBrackets) (value parsed =>
    Parse.givesThen (givesSignInBrackets "','" Comma) (comma found =>
      match comma, found with
        | Some comments, fine =>
          Parse.givesDone
            ((
              ((parsed.left, (never => (Bool.trueNotFalse never).impossible))),
              ((parsed.right.left, fine)),
              parsed.right.right
            ))
        | None, none =>
          Parse.givesDone
            ((
              ((parsed.left, (none => byComputing))),
              ((parsed.right.left, byComputing, byComputing)),
              parsed.right.right
            ))))

theorem givesItemsFrom ∀ (self: Layout → {Parse (Parse.Located Token)} Expr)
    (nested: ∀ (inner: Layout) => Parse.Gives GoodTokens (() => self inner) (ParsedExpr inner))
    (fuel: Nat) (found: List Item)
    (shaped: ShapedItems found)
    (lexical: LexicalItems found)
    (headed: HeadedItems found):
    Parse.Gives GoodTokens (() => itemsFrom fuel self found) ParsedList :=
  match fuel with
    | Zero => Parse.readsFatal _ _
    | Succ more => Parse.givesThen (givesItem self nested) (read parsed =>
      match read, parsed with
        | ({ value, comma }, True), (((valueShaped, bare)), ((valueLexical, commaFine)), valueHeaded) =>
          givesItemsFrom self nested more
            [{ value, comma }, ..found]
            ((valueShaped, shaped))
            ((valueLexical, commaFine, lexical))
            ((valueHeaded, headed))
        | ({ value, comma }, False), (((valueShaped, bare)), ((valueLexical, commaFine)), valueHeaded) =>
          Parse.givesDone
            ((
              ((
                (shapedItemsReverse [{ value, comma }, ..found] ((valueShaped, shaped))),
                (bareLastReverse found { value, comma } (bare byComputing))
              )),
              (lexicalItemsReverse [{ value, comma }, ..found] ((valueLexical, commaFine, lexical))),
              (headedItemsReverse [{ value, comma }, ..found] ((valueHeaded, headed)))
            )))

theorem givesItems ∀ (self: Layout → {Parse (Parse.Located Token)} Expr) (closer: Punctuation)
    (nested: ∀ (inner: Layout) => Parse.Gives GoodTokens (() => self inner) (ParsedExpr inner)):
    Parse.Gives GoodTokens (() => items self closer) ParsedItems :=
  Parse.givesThen (givesSignInBrackets "'${closer.spelling}'" closer) (closed found =>
    match closed, found with
      | Some close, fine => Parse.givesDone ((((((byComputing, byComputing)), byComputing, byComputing)), fine))
      | None, none => Parse.readsWithMark _ _ (at marked =>
        Parse.givesThen (givesItemsFrom self nested at.left [] byComputing byComputing byComputing) (found parsed =>
          Parse.givesThen (givesSign InBrackets "'${closer.spelling}'" closer) (close fine =>
            Parse.givesDone ((parsed, fine))))))

-- Atoms and their calls and fields.

theorem givesAtomOf ∀ (self: Layout → {Parse (Parse.Located Token)} Expr) (layout: Layout)
    (comments: Comments) (kind: Kind)
    (nested: ∀ (inner: Layout) => Parse.Gives GoodTokens (() => self inner) (ParsedExpr inner))
    (fine: Fine comments)
    (goodKind: GoodKind kind):
    Parse.Gives GoodTokens (() => atomOf self comments kind) (ParsedPostfix layout) :=
  match kind, goodKind with
    | Name text, isName => Parse.givesThen givesSkip (skipped done =>
      Parse.givesDone ((((byComputing, byComputing)), ((isName, fine)), byComputing)))
    | Number digits, isDigits => Parse.givesThen givesSkip (skipped done =>
      Parse.givesDone ((((byComputing, byComputing)), ((isDigits, fine)), byComputing)))
    | Str written, isString => Parse.givesThen givesSkip (skipped done =>
      Parse.givesDone ((((byComputing, byComputing)), ((isString, fine)), byComputing)))
    | Sign OpenParen, _ => Parse.givesThen givesSkip (skipped done =>
      Parse.givesThen (nested InBrackets) (inner parsed =>
        Parse.givesThen (givesSign InBrackets "')'" CloseParen) (close closeFine =>
          Parse.givesDone
            ((((byComputing, parsed.left)), ((fine, parsed.right.left, closeFine)), parsed.right.right)))))
    | Sign OpenSquare, _ => Parse.givesThen givesSkip (skipped done =>
      Parse.givesThen (givesItems self CloseSquare nested) (pair parsed =>
        match pair, parsed with
          | (found, close), (((shapedItems, lexicalItems, headedItems)), closeFine) =>
            Parse.givesDone ((((byComputing, shapedItems)), ((fine, lexicalItems, closeFine)), headedItems))))
    | Sign CloseParen, _ => Parse.givesExpected "an expression"
    | Sign CloseSquare, _ => Parse.givesExpected "an expression"
    | Sign Comma, _ => Parse.givesExpected "an expression"
    | Sign Dot, _ => Parse.givesExpected "an expression"
    | Sign Colon, _ => Parse.givesExpected "an expression"
    | Sign Defines, _ => Parse.givesExpected "an expression"
    | Reserved keyword, _ => Parse.givesExpected "an expression"
    | Op operator, _ => Parse.givesExpected "an expression"
    | Stray text, _ => Parse.givesExpected "an expression"

theorem givesAtom ∀ (self: Layout → {Parse (Parse.Located Token)} Expr) (layout: Layout)
    (nested: ∀ (inner: Layout) => Parse.Gives GoodTokens (() => self inner) (ParsedExpr inner)):
    Parse.Gives GoodTokens (() => atom self layout) (ParsedPostfix layout) :=
  Parse.readsPeek _ _ (start fine =>
    match e: start.rest with
      | [] => Parse.givesExpected "an expression"
      | [token, ..later] =>
        match allowed: layout.allows token with
          | True =>
            givesAtomOf self layout
              (layout.comments token)
              token.value.kind
              nested
              (fineComments layout token fine.holds.left)
              fine.holds.left.left
          | False => Parse.givesExpected "an expression")

theorem givesCallAfter ∀ (self: Layout → {Parse (Parse.Located Token)} Expr) (layout: Layout)
    (target: Expr) (open: Comments)
    (nested: ∀ (inner: Layout) => Parse.Gives GoodTokens (() => self inner) (ParsedExpr inner))
    (parsed: ParsedPostfix layout target)
    (fine: Fine open):
    Parse.Gives GoodTokens (() => callAfter self target open) (ParsedPostfix layout) :=
  Parse.givesThen givesSkip (skipped done =>
    Parse.givesThen (givesItems self CloseParen nested) (pair found =>
      match pair, found with
        | (arguments, close), (((shapedArguments, lexicalArguments, headedArguments)), closeFine) =>
          Parse.givesDone
            ((
              ((byComputing, parsed.left.left, parsed.left.right, shapedArguments)),
              ((parsed.right.left, fine, lexicalArguments, closeFine)),
              parsed.right.right,
              headedArguments
            ))))

theorem givesFieldAfter ∀ (layout: Layout) (target: Expr) (dot: Comments)
    (parsed: ParsedPostfix layout target)
    (fine: Fine dot):
    Parse.Gives GoodTokens (() => fieldAfter layout target dot) (ParsedPostfix layout) :=
  Parse.givesThen givesSkip (skipped done =>
    Parse.givesThen (givesName layout) (pair named =>
      match pair, named with
        | (text, nameComments), (isName, nameFine) =>
          Parse.givesDone
            ((
              ((byComputing, parsed.left.left, parsed.left.right)),
              ((parsed.right.left, fine, isName, nameFine)),
              parsed.right.right
            ))))

--| Where `suffixesFrom` stops: it notes what it expected and gives the
--| target.
theorem givesSuffixesStop ∀ (layout: Layout) (target: Expr)
    (parsed: ParsedPostfix layout target):
    Parse.Gives GoodTokens
      (() =>
        Parse.note (Parse.Problem.Expected "'('")
        Parse.note (Parse.Problem.Expected "'.'")
        target)
      (ParsedPostfix layout) :=
  Parse.givesThen (Parse.givesNote (Parse.Problem.Expected "'('")) (noted done =>
    givesNoted (Parse.Problem.Expected "'.'") parsed)

theorem givesSuffixesAfter ∀ (self: Layout → {Parse (Parse.Located Token)} Expr) (layout: Layout) (more: Nat)
    (target: Expr) (tried: () → {Parse (Parse.Located Token)} Expr)
    (parsed: ParsedPostfix layout target)
    (givesTried: Parse.Gives GoodTokens tried (ParsedPostfix layout))
    (givesMore: ∀ (longer: Expr) => ParsedPostfix layout longer
      → Parse.Gives GoodTokens (() => suffixesFrom more self layout longer) (ParsedPostfix layout)):
    Parse.Gives GoodTokens
      (() => suffixesAfter more self layout target (Parse.optional tried))
      (ParsedPostfix layout) :=
  Parse.givesThen (Parse.givesOptional givesTried) (longer found =>
    match longer, found with
      | Some longer, found => givesMore longer found
      | None, _ => Parse.givesDone parsed)

--| What `suffixesFrom` looks at next: the next token's kind and
--| comments if the layout allows it there, whose comments are fine.
theorem givesSuffixNext ∀ (layout: Layout):
    Parse.Gives GoodTokens
      (() =>
        match peek() with
          | Some token if layout.allows token => (token.value.kind, layout.comments token)
          | _ => (Stray "", Comments.none))
      (seen => Fine seen.snd) :=
  Parse.readsPeek _ _ (start fine =>
    match e: start.rest with
      | [] => Parse.givesDone ((byComputing, byComputing))
      | [token, ..later] =>
        match allowed: layout.allows token with
          | True => Parse.givesDone (fineComments layout token fine.holds.left)
          | False => Parse.givesDone ((byComputing, byComputing)))

--| An atom's calls and fields keep it postfix.
theorem givesSuffixes ∀ (self: Layout → {Parse (Parse.Located Token)} Expr) (layout: Layout)
    (nested: ∀ (inner: Layout) => Parse.Gives GoodTokens (() => self inner) (ParsedExpr inner))
    (fuel: Nat) (target: Expr)
    (parsed: ParsedPostfix layout target):
    Parse.Gives GoodTokens (() => suffixesFrom fuel self layout target) (ParsedPostfix layout) :=
  Parse.givesThen (givesSuffixNext layout) (seen fine =>
    match fuel, seen with
      | Zero, (kind, comments) => givesSuffixesStop layout target parsed
      | Succ more, (Sign OpenParen, open) =>
        givesSuffixesAfter self layout more target
          (() => callAfter self target open)
          parsed
          (givesCallAfter self layout target open nested parsed fine)
          (longer longerParsed => givesSuffixes self layout nested more longer longerParsed)
      | Succ more, (Sign Dot, dot) =>
        givesSuffixesAfter self layout more target
          (() => fieldAfter layout target dot)
          parsed
          (givesFieldAfter layout target dot parsed fine)
          (longer longerParsed => givesSuffixes self layout nested more longer longerParsed)
      | Succ more, (Sign CloseParen, comments) => givesSuffixesStop layout target parsed
      | Succ more, (Sign OpenSquare, comments) => givesSuffixesStop layout target parsed
      | Succ more, (Sign CloseSquare, comments) => givesSuffixesStop layout target parsed
      | Succ more, (Sign Comma, comments) => givesSuffixesStop layout target parsed
      | Succ more, (Sign Colon, comments) => givesSuffixesStop layout target parsed
      | Succ more, (Sign Defines, comments) => givesSuffixesStop layout target parsed
      | Succ more, (Name text, comments) => givesSuffixesStop layout target parsed
      | Succ more, (Number digits, comments) => givesSuffixesStop layout target parsed
      | Succ more, (Str written, comments) => givesSuffixesStop layout target parsed
      | Succ more, (Reserved keyword, comments) => givesSuffixesStop layout target parsed
      | Succ more, (Op operator, comments) => givesSuffixesStop layout target parsed
      | Succ more, (Stray text, comments) => givesSuffixesStop layout target parsed)

theorem givesPostfix ∀ (self: Layout → {Parse (Parse.Located Token)} Expr) (layout: Layout)
    (nested: ∀ (inner: Layout) => Parse.Gives GoodTokens (() => self inner) (ParsedExpr inner)):
    Parse.Gives GoodTokens (() => postfix self layout) (ParsedPostfix layout) :=
  Parse.givesThen (Parse.givesNote (Parse.Problem.Expected "an expression")) (noted done =>
    Parse.givesThen (givesAtom self layout nested) (first parsed =>
      Parse.readsWithMark _ _ (at marked => givesSuffixes self layout nested (at.left + 1) first parsed)))

--| `-`s before a postfix expression make an operand.
theorem givesNegations ∀ (self: Layout → {Parse (Parse.Located Token)} Expr) (layout: Layout)
    (nested: ∀ (inner: Layout) => Parse.Gives GoodTokens (() => self inner) (ParsedExpr inner)) (fuel: Nat):
    Parse.Gives GoodTokens (() => negationsFrom fuel self layout) (ParsedOperand layout) :=
  let plain: Parse.Gives GoodTokens (() => postfix self layout) (ParsedOperand layout) :=
    Parse.givesWeaken (givesPostfix self layout nested) (expr parsed =>
      ((((postfixIsOperand expr parsed.left.left), parsed.left.right)), parsed.right))
  Parse.readsPeek _ _ (start fine =>
    match fuel with
      | Zero => plain
      | Succ more =>
        match e: start.rest with
          | [] => plain
          | [token, ..later] =>
            match minus: isMinus layout token with
              | False => plain
              | True => Parse.givesThen givesSkip (skipped done =>
                Parse.givesThen (givesNegations self layout nested more) (inner parsed =>
                  Parse.givesDone
                    ((
                      ((byComputing, parsed.left.left, parsed.left.right)),
                      (((fineComments layout token fine.holds.left), parsed.right.left)),
                      parsed.right.right
                    )))))

theorem givesOperand ∀ (self: Layout → {Parse (Parse.Located Token)} Expr) (layout: Layout)
    (nested: ∀ (inner: Layout) => Parse.Gives GoodTokens (() => self inner) (ParsedExpr inner)):
    Parse.Gives GoodTokens (() => operand self layout) (ParsedOperand layout) :=
  Parse.readsWithMark _ _ (at marked => givesNegations self layout nested (at.left + 1))

-- Operator chains.

--| An operator chain is grouped by precedence, each level chaining from
--| the left, and keeps its operands' texts and heads.
theorem givesChain ∀ (self: Layout → {Parse (Parse.Located Token)} Expr) (layout: Layout)
    (nested: ∀ (inner: Layout) => Parse.Gives GoodTokens (() => self inner) (ParsedExpr inner)):
    Parse.Gives GoodTokens
      (() => Parse.operators "an operator" (operatorLevels layout) (() => operand self layout))
      (ParsedExpr layout) :=
  Parse.readsWeaken
    (Parse.readsOperatorsEvery "an operator"
      (operatorLevels layout)
      (() => operand self layout)
      (ParsedOperand layout)
      (lowest expr => Grouped lowest expr ∧ Lexical expr ∧ HeadedAt layout expr)
      (lowest highest expr => Chained lowest highest expr ∧ Lexical expr ∧ HeadedAt layout expr)
      (givesOperand self layout nested)
      (lowest highest value parsed =>
        (((parsed.left.right, (operandIsChain value parsed.left.left), (Inl parsed.left.left))), parsed.right))
      (lowest highest value chained =>
        (
          ((
            chained.left.left,
            chained.left.right.left,
            (match chained.left.right.right with
              | Inl isOperand => Inl isOperand
              | Inr both => Inr both.left)
          )),
          chained.right
        ))
      (lowest highest level associativity combine item left right good found above below leftChained rightGrouped =>
        (
          (chainStep layout lowest highest level associativity combine item left right found above below
              leftChained.left rightGrouped.left),
          (lexicalStep layout lowest highest level associativity combine item left right good found above below
              leftChained.right.left rightGrouped.right.left),
          (headedStep layout lowest highest level associativity combine item left right found above below
              leftChained.right.right rightGrouped.right.right)
        )))
    (taken value grouped => (grouped.left.left, grouped.right))

-- Bodies and blocks.

theorem givesBare ∀ (self: Layout → {Parse (Parse.Located Token)} Expr) (layout: Layout)
    (nested: ∀ (inner: Layout) => Parse.Gives GoodTokens (() => self inner) (ParsedExpr inner)):
    Parse.Gives GoodTokens (() => bareStatement self layout) (ParsedBare layout) :=
  Parse.givesThen (nested layout) (value parsed =>
    Parse.givesDone
      ((
        (((shapedHeaded layout value parsed.left), byComputing)),
        (((lexicalHeaded layout value parsed.right.left), byComputing)),
        (headedBare layout value parsed.right.right)
      )))

theorem givesInline ∀ (self: Layout → {Parse (Parse.Located Token)} Expr) (layout: Layout)
    (nested: ∀ (inner: Layout) => Parse.Gives GoodTokens (() => self inner) (ParsedExpr inner)):
    Parse.Gives GoodTokens (() => inlineBody self layout) (ParsedBody layout) :=
  Parse.givesThen (givesBare self layout nested) (line parsed =>
    match line, parsed with
      | Bare value, (((shaped, coded)), ((lexical, _)), headed, isBare) =>
        Parse.givesDone
          ((
            ((((shaped, byComputing)), coded)),
            ((((lexical, byComputing)), coded)),
            ((headed, byComputing)),
            byComputing,
            (inside => byComputing)
          ))
      | Let letComments name nameComments equals inner, (_, _, _, never) => (Bool.falseNotTrue never).impossible
      | StatementNote comment, (_, _, _, never) => (Bool.falseNotTrue never).impossible)

--| A statement's line at the statement's own start: a `let` takes its
--| keyword's comments there, where there are none above.
theorem givesStatementLine ∀ (self: Layout → {Parse (Parse.Located Token)} Expr)
    (nested: ∀ (inner: Layout) => Parse.Gives GoodTokens (() => self inner) (ParsedExpr inner)) (fuel: Nat)
    (givesBody: ∀ (inner: Layout) => Parse.Gives GoodTokens (() => bodyFuel fuel self inner) (ParsedBody inner))
    (column start: Nat) (first: Parse.Located Token) (kind: Kind)
    (fine: Fine ((InStatement column start).comments first))
    (noAbove: ((InStatement column start).comments first).above = []):
    Parse.Gives GoodTokens (() => statementLine fuel self (InStatement column start) first kind) ParsedLine :=
  let bare: Parse.Gives GoodTokens (() => bareStatement self (InStatement column start)) ParsedLine :=
    Parse.givesWeaken (givesBare self (InStatement column start) nested) (line parsed =>
      (parsed.left, parsed.right.left, parsed.right.right.left))
  match kind with
    | Reserved LetKeyword => Parse.givesThen givesSkip (skipped done =>
      Parse.givesThen (givesName (InStatement column start)) (pair named =>
        match pair, named with
          | (bound, nameComments), (isName, nameFine) =>
            Parse.givesThen (givesSign (InStatement column start) "'='" Defines) (equals equalsFine =>
              Parse.givesThen (givesBody (InStatement column start)) (inner parsed =>
                Parse.givesDone
                  ((
                    ((parsed.left, byComputing)),
                    ((((fine, isName, nameFine, equalsFine, parsed.right.left)), byComputing)),
                    noAbove,
                    parsed.right.right
                  ))))))
    | Reserved FnKeyword => bare
    | Reserved IfKeyword => bare
    | Reserved ThenKeyword => bare
    | Reserved ElseKeyword => bare
    | Reserved TakesKeyword => bare
    | Name text => bare
    | Number digits => bare
    | Str written => bare
    | Sign punctuation => bare
    | Op operator => bare
    | Stray text => bare

theorem givesStatement ∀ (self: Layout → {Parse (Parse.Located Token)} Expr)
    (nested: ∀ (inner: Layout) => Parse.Gives GoodTokens (() => self inner) (ParsedExpr inner)) (fuel: Nat)
    (givesBody: ∀ (inner: Layout) => Parse.Gives GoodTokens (() => bodyFuel fuel self inner) (ParsedBody inner))
    (column: Nat):
    Parse.Gives GoodTokens (() => statement fuel self column) ParsedLines :=
  Parse.readsWithMark _ _ (start fine =>
    match e: start.rest with
      | [] => Parse.readsStop _
      | [first, ..later] =>
        match starts: first.value.startsLine && first.value.column == column with
          | False => Parse.readsStop _
          | True =>
            Parse.givesThen
              (givesStatementLine self nested fuel givesBody column first.offset first first.value.kind
                (fineComments (InStatement column first.offset) first fine.holds.left)
                (startAbove column first))
              (line parsed =>
                Parse.givesDone
                  ((
                    ((
                      (shapedNoted first.value.above line parsed.left.left),
                      (closedNoted first.value.above line parsed.left.right)
                    )),
                    ((
                      (lexicalNoted first.value.above line fine.holds.left.right.left parsed.right.left.left),
                      (closedNoted first.value.above line parsed.left.right)
                    )),
                    (headedNoted first.value.above line parsed.right.right)
                  ))))

theorem givesBlock ∀ (self: Layout → {Parse (Parse.Located Token)} Expr)
    (nested: ∀ (inner: Layout) => Parse.Gives GoodTokens (() => self inner) (ParsedExpr inner)) (fuel: Nat)
    (givesBody: ∀ (inner: Layout) => Parse.Gives GoodTokens (() => bodyFuel fuel self inner) (ParsedBody inner))
    (column: Nat):
    Parse.Gives GoodTokens (() => block fuel self column) ParsedBlock :=
  Parse.givesThen (Parse.givesMany1 (givesStatement self nested fuel givesBody column)) (lines all =>
    let shaped := List.allImplies ParsedLines ClosedShaped (group parsed => parsed.left) lines.toList all
    let lexical := List.allImplies ParsedLines ClosedLexical (group parsed => parsed.right.left) lines.toList all
    let headed := List.allImplies ParsedLines (HeadedLines False) (group parsed => parsed.right.right) lines.toList all
    let closed := closedConcat lines.head lines.tail shaped
    Parse.givesDone
      ((
        ((
          (shapedWithoutFirstBlank lines.toList.concat (shapedConcat lines.toList shaped)),
          (closedWithoutFirstBlank lines.toList.concat closed)
        )),
        ((
          (lexicalWithoutFirstBlank lines.toList.concat (lexicalConcat lines.toList lexical)),
          (closedWithoutFirstBlank lines.toList.concat closed)
        )),
        (headedWithoutFirstBlank lines.toList.concat (headedConcat lines.toList headed)),
        (unspacedWithout lines.toList.concat),
        (never => (Bool.falseNotTrue never).impossible)
      )))

--| A body, a block or one expression.
theorem givesBodyFuel ∀ (self: Layout → {Parse (Parse.Located Token)} Expr)
    (nested: ∀ (inner: Layout) => Parse.Gives GoodTokens (() => self inner) (ParsedExpr inner))
    (fuel: Nat) (layout: Layout):
    Parse.Gives GoodTokens (() => bodyFuel fuel self layout) (ParsedBody layout) :=
  Parse.readsPeek _ _ (start fine =>
    match fuel with
      | Zero => Parse.readsFatal _ _
      | Succ more =>
        match layout with
          | InBrackets => givesInline self InBrackets nested
          | InStatement column at =>
            match e: start.rest with
              | [] => givesInline self (InStatement column at) nested
              | [token, ..later] =>
                match deeper: token.value.startsLine && token.value.column > column with
                  | False => givesInline self (InStatement column at) nested
                  | True =>
                    givesBlock self nested more (inner => givesBodyFuel self nested more inner) token.value.column)

theorem givesBody ∀ (self: Layout → {Parse (Parse.Located Token)} Expr) (layout: Layout)
    (nested: ∀ (inner: Layout) => Parse.Gives GoodTokens (() => self inner) (ParsedExpr inner)):
    Parse.Gives GoodTokens (() => body self layout) (ParsedBody layout) :=
  Parse.readsWithMark _ _ (at marked => givesBodyFuel self nested (at.left + 1) layout)

-- `if`, and the expression parser.

theorem givesElse ∀ (layout: Layout): Parse.Gives GoodTokens (() => elseKeyword layout) Fine :=
  Parse.readsPeek _ _ (start fine =>
    match e: start.rest with
      | [] => givesKeyword layout ElseKeyword
      | [token, ..later] =>
        match isElse: (keywordIs ElseKeyword token.value.kind).isSome with
          | False => givesKeyword layout ElseKeyword
          | True =>
            match allowed: layout.allowsElse token with
              | True =>
                Parse.givesThen givesSkip (skipped done => Parse.givesDone (fineComments layout token fine.holds.left))
              | False => Parse.readsFail _ _)

--| One level of the expression parser, given that `self` gives what it
--| should for the expressions nested in it.
theorem givesExpressionRule ∀ (self: Layout → {Parse (Parse.Located Token)} Expr) (layout: Layout)
    (nested: ∀ (inner: Layout) => Parse.Gives GoodTokens (() => self inner) (ParsedExpr inner)):
    Parse.Gives GoodTokens (() => expressionRule self layout) (ParsedExpr layout) :=
  Parse.readsPeek _ _ (start fine =>
    match e: start.rest with
      | [] => givesChain self layout nested
      | [token, ..later] =>
        match found: isIf layout token with
          | False => givesChain self layout nested
          | True => Parse.givesThen givesSkip (skipped done =>
            Parse.givesThen (nested layout) (condition conditionParsed =>
              Parse.givesThen (givesKeyword layout ThenKeyword) (thenComments thenFine =>
                Parse.givesThen (givesBody self layout nested) (whenTrue trueParsed =>
                  Parse.givesThen (givesElse layout) (elseComments elseFine =>
                    Parse.givesThen (givesBody self layout nested) (whenFalse falseParsed =>
                      Parse.givesDone
                        ((
                          ((conditionParsed.left, trueParsed.left, falseParsed.left)),
                          ((
                            (fineComments layout token fine.holds.left),
                            conditionParsed.right.left,
                            thenFine,
                            trueParsed.right.left,
                            elseFine,
                            falseParsed.right.left
                          )),
                          conditionParsed.right.right,
                          trueParsed.right.right,
                          falseParsed.right.right
                        )))))))))

--| Every expression the parser gives from good tokens: of the parser's
--| shape, with the lexer's texts, headed as its layout is.
theorem givesExpression ∀ (layout: Layout): Parse.Gives GoodTokens (() => expression layout) (ParsedExpr layout) :=
  Parse.givesRecursiveWith expressionRule ParsedExpr
    (self nested argument => givesExpressionRule self argument nested)
    layout

-- Declarations and the file.

-- Types and parameter groups.

theorem givesTypeOf ∀ (self: () → {Parse (Parse.Located Token)} TypeExpr) (comments: Comments) (kind: Kind)
    (nested: ∀ (inner: ()) => Parse.Gives GoodTokens (() => self inner) LexicalType)
    (fine: Fine comments)
    (goodKind: GoodKind kind):
    Parse.Gives GoodTokens (() => typeOf self comments kind) LexicalType :=
  match kind, goodKind with
    | Name text, isName => Parse.givesThen givesSkip (skipped done => Parse.givesDone ((isName, fine)))
    | Sign OpenParen, _ => Parse.givesThen givesSkip (skipped done =>
      Parse.givesThen (nested ()) (inner lexical =>
        Parse.givesThen (givesSign InBrackets "')'" CloseParen) (close closeFine =>
          Parse.givesDone ((fine, lexical, closeFine)))))
    | Sign CloseParen, _ => Parse.givesExpected "a type"
    | Sign OpenSquare, _ => Parse.givesExpected "a type"
    | Sign CloseSquare, _ => Parse.givesExpected "a type"
    | Sign Comma, _ => Parse.givesExpected "a type"
    | Sign Dot, _ => Parse.givesExpected "a type"
    | Sign Colon, _ => Parse.givesExpected "a type"
    | Sign Defines, _ => Parse.givesExpected "a type"
    | Number digits, _ => Parse.givesExpected "a type"
    | Str written, _ => Parse.givesExpected "a type"
    | Reserved keyword, _ => Parse.givesExpected "a type"
    | Op operator, _ => Parse.givesExpected "a type"
    | Stray text, _ => Parse.givesExpected "a type"

--| Every type the parser gives from good tokens has the lexer's texts.
theorem givesTypeExpr: Parse.Gives GoodTokens (() => typeExpr()) LexicalType :=
  Parse.givesRecursiveWith typeRule (unit found => LexicalType found)
    (self nested unit =>
      Parse.readsPeek _ _ (start fine =>
        match e: start.rest with
          | [] => Parse.givesExpected "a type"
          | [token, ..later] =>
            givesTypeOf self
              (Layout.comments InBrackets token)
              token.value.kind
              nested
              (fineComments InBrackets token fine.holds.left)
              fine.holds.left.left))
    ()

theorem givesTyping: Parse.Gives GoodTokens typing ((found: (Comments, TypeExpr)) => Fine found.fst ∧ LexicalType found.snd) :=
  Parse.givesThen (givesSign InBrackets "':'" Colon) (colon colonFine =>
    Parse.givesThen givesTypeExpr (annotation lexical => Parse.givesDone ((colonFine, lexical))))

theorem givesGroupOf ∀ (first: (Text, Comments)) (others: List (Text, Comments))
    (typed: Option (Comments, TypeExpr))
    (named: FineNamed first)
    (more: List.All FineNamed others)
    (typedFine: Parse.Perhaps ((found: (Comments, TypeExpr)) => Fine found.fst ∧ LexicalType found.snd) typed):
    Parse.Gives GoodTokens (() => groupOf first others typed) LexicalGroup :=
  match typed, typedFine, others with
    | Some (colon, annotation), Both colonFine lexical, _ =>
      Parse.givesDone ((named, (lexicalNamesOf others more), colonFine, lexical))
    | None, _, [] => Parse.givesDone named
    | None, _, [_, .._] => Parse.givesExpected "':'"

theorem givesGroup: Parse.Gives GoodTokens parameterGroup LexicalGroup :=
  Parse.givesThen (givesName InBrackets) (first named =>
    Parse.givesThen (Parse.givesMany (givesName InBrackets)) (others more =>
      Parse.givesThen (Parse.givesOptional givesTyping) (typed typedFine =>
        givesGroupOf first others typed named more typedFine)))

-- Declarations and the file.

theorem givesParameterStep: Parse.Gives GoodTokens parameterStep FineStep :=
  Parse.givesThen (givesSign InBrackets "','" Comma) (comma commaFine =>
    Parse.givesThen givesGroup (group grouped => Parse.givesDone ((commaFine, grouped))))

theorem givesParameterList: Parse.Gives GoodTokens parameterList FineList :=
  Parse.givesThen givesGroup (first grouped =>
    Parse.givesThen (Parse.givesMany givesParameterStep) (others steps => Parse.givesDone ((grouped, steps))))

theorem givesParameters: Parse.Gives GoodTokens (() => parametersOf (Parse.optional parameterList)) ParsedParameters :=
  Parse.givesThen (Parse.givesOptional givesParameterList) (found listed =>
    match found, listed with
      | None, _ => Parse.givesDone ((byComputing, byComputing))
      | Some (first, others), Both grouped steps =>
        Parse.givesDone (((withCommasBare first others), (lexicalWithCommas first others grouped steps))))

--| A function's header: `takes`, the brackets and the parameters, each
--| as the parser gives them.
def ParsedHeader (header: Header): Prop :=
  FineTakes header.takes ∧ Fine header.open ∧ ParsedParameters header.parameters ∧ Fine header.close

theorem givesHeader ∀ (layout: Layout): Parse.Gives GoodTokens (() => functionHeader layout) ParsedHeader :=
  Parse.givesThen (Parse.givesOptional (givesKeyword layout TakesKeyword)) (takes takesFine =>
    Parse.givesThen (givesSign layout "'('" OpenParen) (open openFine =>
      Parse.givesThen givesParameters (parameters listed =>
        Parse.givesThen (givesSign InBrackets "')'" CloseParen) (close closeFine =>
          Parse.givesDone ((takesFine, openFine, listed, closeFine))))))

theorem givesFunctionLine ∀ (column start: Nat) (first: Parse.Located Token)
    (fine: Fine ((InStatement column start).comments first))
    (noAbove: ((InStatement column start).comments first).above = []):
    Parse.Gives GoodTokens (() => functionLine (InStatement column start) first) ParsedDeclaration :=
  Parse.givesThen givesSkip (skipped done =>
    Parse.givesThen (givesName (InStatement column start)) (pair named =>
      match pair, named with
        | (declared, nameComments), (isName, nameFine) =>
          Parse.givesThen (givesHeader (InStatement column start)) (read headed =>
            match headed with
              | (takesFine, openFine, listed, closeFine) =>
                Parse.givesThen (givesSign (InStatement column start) "'='" Defines) (equals equalsFine =>
                  Parse.givesThen (givesBody expression (InStatement column start) givesExpression) (inner parsed =>
                    Parse.givesDone
                      ((
                        ((listed.left, parsed.left)),
                        ((
                          fine,
                          isName,
                          nameFine,
                          takesFine,
                          openFine,
                          listed.right,
                          closeFine,
                          equalsFine,
                          parsed.right.left
                        )),
                        noAbove,
                        parsed.right.right
                      )))))))

theorem givesValueLine ∀ (column start: Nat) (first: Parse.Located Token)
    (fine: Fine ((InStatement column start).comments first))
    (noAbove: ((InStatement column start).comments first).above = []):
    Parse.Gives GoodTokens (() => valueLine (InStatement column start) first) ParsedDeclaration :=
  Parse.givesThen givesSkip (skipped done =>
    Parse.givesThen (givesName (InStatement column start)) (pair named =>
      match pair, named with
        | (declared, nameComments), (isName, nameFine) =>
          Parse.givesThen (givesSign (InStatement column start) "'='" Defines) (equals equalsFine =>
            Parse.givesThen (givesBody expression (InStatement column start) givesExpression) (inner parsed =>
              Parse.givesDone
                ((
                  parsed.left,
                  ((fine, isName, nameFine, equalsFine, parsed.right.left)),
                  noAbove,
                  parsed.right.right
                ))))))

--| Not a declaration: what `declarationLine` does at any other token.
theorem givesNoDeclaration: Parse.Gives GoodTokens
      (() =>
        Parse.note (Parse.Problem.Literal "fn")
        Parse.note (Parse.Problem.Literal "let")
        Empty.absurd Parse.stop())
      ParsedDeclaration :=
  Parse.givesThen (Parse.givesNote (Parse.Problem.Literal "fn")) (noted done =>
    Parse.givesThen (Parse.givesNote (Parse.Problem.Literal "let")) (noted done => Parse.readsStop _))

theorem givesDeclarationLine ∀ (column start: Nat) (first: Parse.Located Token)
    (fine: Fine ((InStatement column start).comments first))
    (noAbove: ((InStatement column start).comments first).above = []):
    Parse.Gives GoodTokens (() => declarationLine (InStatement column start) first) ParsedDeclaration :=
  match kind: first.value.kind with
    | Reserved FnKeyword => givesFunctionLine column start first fine noAbove
    | Reserved LetKeyword => givesValueLine column start first fine noAbove
    | Reserved IfKeyword => givesNoDeclaration
    | Reserved ThenKeyword => givesNoDeclaration
    | Reserved ElseKeyword => givesNoDeclaration
    | Reserved TakesKeyword => givesNoDeclaration
    | Name text => givesNoDeclaration
    | Number digits => givesNoDeclaration
    | Str written => givesNoDeclaration
    | Sign punctuation => givesNoDeclaration
    | Op operator => givesNoDeclaration
    | Stray text => givesNoDeclaration

theorem givesDeclaration: Parse.Gives GoodTokens declaration ParsedDeclarations :=
  Parse.readsWithMark _ _ (start fine =>
    match e: start.rest with
      | [] => Parse.readsStop _
      | [first, ..later] =>
        match starts: first.value.startsLine && first.value.column == 0 with
          | False => Parse.readsStop _
          | True =>
            Parse.givesThen
              (givesDeclarationLine 0 first.offset first
                (fineComments (InStatement 0 first.offset) first fine.holds.left)
                (startAbove 0 first))
              (parsed found =>
                Parse.givesDone
                  ((
                    (shapedNotedDeclaration first.value.above parsed found.left),
                    (lexicalNotedDeclaration first.value.above parsed fine.holds.left.right.left found.right.left),
                    (headedNotedDeclaration first.value.above parsed found.right.right)
                  ))))

theorem givesFileEnd ∀ (declarations: List (Spaced Declaration)) (endTrivia: List Trivia)
    (fineEnd: FineTrivia endTrivia)
    (parsed: ParsedDeclarations declarations):
    Parse.Gives GoodTokens (() => fileEnd declarations endTrivia) Parsed :=
  let done: Parse.Gives GoodTokens (() => fileOf declarations endTrivia) Parsed :=
    Parse.givesDone
      ((
        (shapedFileOf declarations endTrivia parsed.left),
        (lexicalFileOf declarations endTrivia fineEnd parsed.right.left),
        (headedFileOf declarations endTrivia parsed.right.right)
      ))
  Parse.readsPeek _ _ (start fine =>
    match e: start.rest with
      | [] => done
      | [token, ..later] =>
        match indented: token.value.startsLine && token.value.column > 0 with
          | False => done
          | True => Parse.readsFail _ _)

theorem givesSourceFile ∀ (endTrivia: List Trivia)
    (fineEnd: FineTrivia endTrivia):
    Parse.Gives GoodTokens (() => sourceFile endTrivia) Parsed :=
  Parse.givesThen (Parse.givesMany givesDeclaration) (found all =>
    givesFileEnd found.concat endTrivia fineEnd
      ((
        (declarationsConcat found
          (List.allImplies ParsedDeclarations ShapedDeclarations (lines p => p.left) found all)),
        (lexicalDeclarationsConcat found
          (List.allImplies ParsedDeclarations LexicalDeclarations (lines p => p.right.left) found all)),
        (headedDeclarationsConcat found
          (List.allImplies ParsedDeclarations HeadedDeclarations (lines p => p.right.right) found all))
      )))

-- From the source.

--| What the parser guarantees about its trees: every file `parse` gives,
--| whatever the source, is `ShapedFile`, `LexicalFile` and `HeadedFile`.
--| The lexer's tokens are `Good` (`lexTexts`), and the walk gives all
--| three from good tokens.
theorem parseParsed ∀ (source: Text) (file: SourceFile) (parsed: parse source = Ok file): Parsed file :=
  match lexed: lex source with
    | Ok tokens =>
      match whole: Parse.whole tokens.tokens (() => sourceFile tokens.endTrivia) with
        | Ok found =>
          let same: found = file := Result.okInjective parsed
          let texts := lexTexts source tokens lexed
          rewrite <- same then
            Parse.wholeReadsIn tokens.tokens
              (() => sourceFile tokens.endTrivia)
              (taken value => Parsed value)
              found
              (givesSourceFile tokens.endTrivia texts.right)
              { holds = goodTokens tokens.tokens texts.left }
              whole

--| What the parser guarantees about its trees: in every file `parse`
--| gives, whatever the source, every expression is of the parser's shape
--| (`Shaped`: operators grouped by precedence and chaining from the left,
--| a call's callee and a field's target postfix, `-` before an operand),
--| in every declaration, block and branch; every body (after `=`, `then`
--| and `else`) ends in a statement, not a comment line (`ClosedLines`);
--| a function's last parameter has no comma's comments (`BareLast`), and
--| neither has the last item of a list or the last argument of a call
--| (`BareLastItem`).
--| So the read-back theorems' `Shaped` hypotheses hold of every parsed
--| tree, with no check at run time.
theorem parseShaped ∀ (source: Text) (file: SourceFile) (parsed: parse source = Ok file): ShapedFile file :=
  (parseParsed source file parsed).left

--| What the parser guarantees about its trees' texts: in every file
--| `parse` gives, whatever the source, every name is a word that spells
--| no keyword, every number is digits, every string is closed by its
--| second quote whatever follows, every comment is `--` and the rest of
--| its line, and every body ends in a statement (`LexicalFile`). So the
--| printer's lexing theorems hold of every parsed tree, with no check at
--| run time.
theorem parseLexical ∀ (source: Text) (file: SourceFile) (parsed: parse source = Ok file): LexicalFile file :=
  (parseParsed source file parsed).right.left

--| What the parser guarantees of where comments and blocks are: in
--| every file `parse` gives, whatever the source, outside brackets no
--| statement's, declaration's or one-expression body's first token holds
--| comments above it in the tree (above a statement or declaration they
--| are the list's comment lines); inside brackets every body is one
--| expression; and no body, and not the file, keeps a blank line above
--| its first line. So the spelling theorems' `Headed` hypotheses hold of
--| every parsed tree, with no check at run time.
theorem parseHeaded ∀ (source: Text) (file: SourceFile) (parsed: parse source = Ok file): HeadedFile file :=
  (parseParsed source file parsed).right.right
