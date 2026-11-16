--| What the parser guarantees of where comments and blocks are
--| (`HeadedFile`, SpellProofs.sw): outside brackets no statement's,
--| declaration's or one-expression body's first token holds comments
--| above it in the tree; inside brackets every body is one expression;
--| and no body or file keeps a blank line above its first line. So the
--| spelling theorems' `Headed` hypotheses hold of every parsed tree and
--| needn't be checked.
--|
--| The walk is `ShapeProofs.sw`'s, over the same parser functions. The
--| first-token facts need no account of the tokens read: `bareStatement`
--| clears the comments on the tree it built (`Layout.headed`), and a
--| `let` or `fn` takes its keyword's comments at the statement's own
--| start, where `Layout.comments` gives none above.

namespace Toy.Fmt.Proofs
import Toy.Syntax (..)
import Toy.Syntax.Proofs (..)
import Toy.Fmt (..)
import Std (Bool, Eq, List, NonEmptyList, Option, Parse, Result, Text, Void)

--| `HeadedExpr` of an expression read at `layout`.
def HeadedAt (layout: Layout) (expr: Expr): Prop := HeadedExpr (bracketedOf layout) expr

--| `HeadedBody` of a body read at `layout`.
def HeadedBodyAt (layout: Layout) (found: Body): Prop := HeadedBody (bracketedOf layout) found

-- Clearing.

theorem clearedFirstAbove ∀ (expr: Expr): expr.withoutFirstAbove.firstAbove = [] := match expr with
  | Var _ _ => rfl
  | NumberLiteral _ _ => rfl
  | StringLiteral _ _ => rfl
  | Bracketed _ _ _ => rfl
  | ListLiteral _ _ _ => rfl
  | Call callee _ _ _ => clearedFirstAbove callee
  | Field target _ _ _ => clearedFirstAbove target
  | Negate _ _ => rfl
  | Binary _ _ left _ => clearedFirstAbove left
  | If _ _ _ _ _ _ => rfl

theorem headedCleared ∀ (bracketed: Bool) (expr: Expr)
    (headed: HeadedExpr bracketed expr):
    HeadedExpr bracketed expr.withoutFirstAbove :=
  match expr, headed with
    | Var name comments, headed => headed
    | NumberLiteral digits comments, headed => headed
    | StringLiteral written comments, headed => headed
    | Bracketed open inner close, headed => headed
    | ListLiteral open items close, headed => headed
    | Call callee open arguments close, Both calleeHeaded others =>
      Both (headedCleared bracketed callee calleeHeaded) others
    | Field target dot name nameComments, headed => headedCleared bracketed target headed
    | Negate minus operand, headed => headed
    | Binary operator sign left right, Both leftHeaded rightHeaded =>
      Both (headedCleared bracketed left leftHeaded) rightHeaded
    | If ifComments condition thenComments whenTrue elseComments whenFalse, headed => headed

--| A statement that is an expression.
def IsBare: Statement → Prop
  | Bare _ => True
  | _ => False

--| What `bareStatement` gives at a layout inside brackets or not.
def BareHeaded (bracketed: Bool) (line: Statement): Prop := HeadedStatement bracketed line ∧ IsBare line

theorem headedBare ∀ (layout: Layout) (value: Expr)
    (headed: HeadedAt layout value):
    BareHeaded (bracketedOf layout) (Bare (layout.headed value)) :=
  match layout, headed with
    | InBrackets, headed => Both (Both (never => Void.exfalso (Bool.trueNotFalse never)) headed) rfl
    | InStatement column start, headed =>
      Both (Both (outside => clearedFirstAbove value) (headedCleared False value headed)) rfl

-- Items.

theorem headedItemsAppend ∀ (front: List Item) (last: Item)
    (headed: HeadedItems front)
    (lastHeaded: HeadedExpr True last.value):
    HeadedItems (front ++ [last]) :=
  match front, headed, last, lastHeaded with
    | [], headed, { value, comma }, lastHeaded => Both lastHeaded rfl
    | [{ value, comma }, ..rest], Both valueHeaded restHeaded, last, lastHeaded =>
      Both valueHeaded (headedItemsAppend rest last restHeaded lastHeaded)

theorem headedItemsReverse ∀ (found: List Item) (headed: HeadedItems found): HeadedItems found.reverse :=
  match found, headed with
    | [], headed => rfl
    | [{ value, comma }, ..rest], Both valueHeaded restHeaded =>
      rewrite List.reverseCons ({ value, comma }: Item) rest in
        headedItemsAppend rest.reverse { value, comma } (headedItemsReverse rest restHeaded) valueHeaded

def HeadedItem (read: (Item, Bool)): Prop := HeadedExpr True read.fst.value

theorem givesHeadedItem ∀ (self: Layout → {Parse (Parse.Located Token)} Expr)
    (nested: ∀ (inner: Layout) => Gives (() => self inner) (HeadedAt inner)):
    Gives (() => item self) HeadedItem :=
  givesThen
    (() => self InBrackets)
    (value =>
      let comma := signInBrackets "','" Comma
      ({ value, comma = comma.getOrElse Comments.none }, comma.isSome))
    (HeadedExpr True)
    HeadedItem
    (nested InBrackets)
    (value headed =>
      givesThen
        (() => signInBrackets "','" Comma)
        (comma => ({ value, comma = comma.getOrElse Comments.none }, comma.isSome))
        (comma => True)
        HeadedItem
        (givesSignInBrackets "','" Comma)
        (comma found => givesDone _ HeadedItem headed))

theorem givesHeadedItemsFrom ∀ (self: Layout → {Parse (Parse.Located Token)} Expr)
    (nested: ∀ (inner: Layout) => Gives (() => self inner) (HeadedAt inner))
    (fuel: Nat) (found: List Item)
    (headed: HeadedItems found):
    Gives (() => itemsFrom fuel self found) HeadedItems :=
  match fuel with
    | Zero => givesDone [] HeadedItems rfl
    | Succ more =>
      givesThen
        (() => item self)
        (itemsAfter more self found)
        HeadedItem
        HeadedItems
        (givesHeadedItem self nested)
        (read itemHeaded =>
          match read, itemHeaded with
            | ({ value, comma }, True), valueHeaded =>
              givesHeadedItemsFrom self nested more [{ value, comma }, ..found] (Both valueHeaded headed)
            | ({ value, comma }, False), valueHeaded =>
              givesDone _ HeadedItems (headedItemsReverse [{ value, comma }, ..found] (Both valueHeaded headed)))

theorem givesHeadedItems ∀ (self: Layout → {Parse (Parse.Located Token)} Expr) (closer: Punctuation)
    (nested: ∀ (inner: Layout) => Gives (() => self inner) (HeadedAt inner)):
    Gives (() => items self closer) (found => HeadedItems found.fst) :=
  Parse.readsThen (givesSignInBrackets "'${closer.spelling}'" closer) (firstRead closed facts =>
    match closed with
      | Some close => Parse.readsDone ([], close) _ rfl
      | None =>
        givesThen
          (() => Parse.mark())
          (at =>
            let found := itemsFrom at.left self []
            let close := sign InBrackets "'${closer.spelling}'" closer
            (found, close))
          (at => True)
          (found => HeadedItems found.fst)
          givesMark
          (at marked =>
            givesThen
              (() => itemsFrom at.left self [])
              (found =>
                let close := sign InBrackets "'${closer.spelling}'" closer
                (found, close))
              HeadedItems
              (found => HeadedItems found.fst)
              (givesHeadedItemsFrom self nested at.left [] rfl)
              (found headed =>
                givesThen
                  (() => sign InBrackets "'${closer.spelling}'" closer)
                  (close => (found, close))
                  (close => True)
                  (found => HeadedItems found.fst)
                  (givesSign InBrackets "'${closer.spelling}'" closer)
                  (close signed => givesDone _ _ headed))))

-- Atoms and their calls and fields.

theorem givesHeadedAtomOf ∀ (self: Layout → {Parse (Parse.Located Token)} Expr) (bracketed: Bool)
    (comments: Comments) (kind: Kind)
    (nested: ∀ (inner: Layout) => Gives (() => self inner) (HeadedAt inner)):
    Gives (() => atomOf self comments kind) (HeadedExpr bracketed) :=
  match kind with
    | Name text =>
      givesThen
        (() => skip())
        (skipped => Var text comments)
        (skipped => True)
        (HeadedExpr bracketed)
        givesSkip
        (skipped done => givesDone _ (HeadedExpr bracketed) rfl)
    | Number digits =>
      givesThen
        (() => skip())
        (skipped => NumberLiteral digits comments)
        (skipped => True)
        (HeadedExpr bracketed)
        givesSkip
        (skipped done => givesDone _ (HeadedExpr bracketed) rfl)
    | Str written =>
      givesThen
        (() => skip())
        (skipped => StringLiteral written comments)
        (skipped => True)
        (HeadedExpr bracketed)
        givesSkip
        (skipped done => givesDone _ (HeadedExpr bracketed) rfl)
    | Sign OpenParen =>
      givesThen
        (() => skip())
        (skipped =>
          let inner := self InBrackets
          let close := sign InBrackets "')'" CloseParen
          Bracketed comments inner close)
        (skipped => True)
        (HeadedExpr bracketed)
        givesSkip
        (skipped done =>
          givesThen
            (() => self InBrackets)
            (inner =>
              let close := sign InBrackets "')'" CloseParen
              Bracketed comments inner close)
            (HeadedExpr True)
            (HeadedExpr bracketed)
            (nested InBrackets)
            (inner headed =>
              givesThen
                (() => sign InBrackets "')'" CloseParen)
                (close => Bracketed comments inner close)
                (close => True)
                (HeadedExpr bracketed)
                (givesSign InBrackets "')'" CloseParen)
                (close signed => givesDone _ (HeadedExpr bracketed) headed)))
    | Sign OpenSquare => Parse.readsThen givesSkip (skipRead skipped done =>
      Parse.readsThen (givesHeadedItems self CloseSquare nested) (itemsRead pair headed =>
        match pair, headed with
          | (found, close), headed => Parse.readsDone (ListLiteral comments found close) _ headed))
    | Sign CloseParen => givesExpected "an expression" (HeadedExpr bracketed)
    | Sign CloseSquare => givesExpected "an expression" (HeadedExpr bracketed)
    | Sign Comma => givesExpected "an expression" (HeadedExpr bracketed)
    | Sign Dot => givesExpected "an expression" (HeadedExpr bracketed)
    | Sign Defines => givesExpected "an expression" (HeadedExpr bracketed)
    | Reserved keyword => givesExpected "an expression" (HeadedExpr bracketed)
    | Op operator => givesExpected "an expression" (HeadedExpr bracketed)
    | Stray text => givesExpected "an expression" (HeadedExpr bracketed)

theorem givesHeadedAtom ∀ (self: Layout → {Parse (Parse.Located Token)} Expr) (layout: Layout)
    (nested: ∀ (inner: Layout) => Gives (() => self inner) (HeadedAt inner)):
    Gives (() => atom self layout) (HeadedAt layout) :=
  Parse.readsInOfRuns (total state value after fine honest h =>
    match e: state.at.rest with
      | [token, ..later] =>
        match allowed: layout.allows token with
          | True =>
            givesHeadedAtomOf self
              (bracketedOf layout)
              (layout.comments token)
              token.value.kind
              nested
              state.at
              fine
              total
              state
              value
              after
              rfl
              honest
              h)

theorem givesHeadedCall ∀ (self: Layout → {Parse (Parse.Located Token)} Expr) (bracketed: Bool)
    (target: Expr) (open: Comments)
    (nested: ∀ (inner: Layout) => Gives (() => self inner) (HeadedAt inner))
    (headed: HeadedExpr bracketed target):
    Gives (() => callAfter self target open) (HeadedExpr bracketed) :=
  Parse.readsThen givesSkip (skipRead skipped done =>
    Parse.readsThen (givesHeadedItems self CloseParen nested) (itemsRead pair itemsHeaded =>
      match pair, itemsHeaded with
        | (arguments, close), itemsHeaded =>
          Parse.readsDone (Call target open arguments close) _ (Both headed itemsHeaded)))

theorem givesHeadedField ∀ (bracketed: Bool) (layout: Layout) (target: Expr) (dot: Comments)
    (headed: HeadedExpr bracketed target):
    Gives (() => fieldAfter layout target dot) (HeadedExpr bracketed) :=
  Parse.readsThen givesSkip (skipRead skipped done =>
    Parse.readsThen (givesName layout) (nameRead pair named =>
      match pair with | (text, nameComments) => Parse.readsDone (Field target dot text nameComments) _ headed))

theorem givesHeadedStop ∀ (layout: Layout) (target: Expr)
    (headed: HeadedAt layout target):
    Gives
      (() =>
        Parse.note (Parse.Problem.Expected "'('")
        Parse.note (Parse.Problem.Expected "'.'")
        target)
      (HeadedAt layout) :=
  givesThen
    (() => Parse.note (Parse.Problem.Expected "'('"))
    (noted =>
      Parse.note (Parse.Problem.Expected "'.'")
      target)
    (noted => True)
    (HeadedAt layout)
    (Parse.readsWeaken (Parse.readsNote (Parse.Problem.Expected "'('")) (taken noted none => rfl))
    (noted done => givesNoted (Parse.Problem.Expected "'.'") target (HeadedAt layout) headed)

theorem givesHeadedSuffixesAfter ∀ (self: Layout → {Parse (Parse.Located Token)} Expr) (layout: Layout) (more: Nat)
    (target: Expr) (tried: () → {Parse (Parse.Located Token)} Expr)
    (headed: HeadedAt layout target)
    (givesTried: Gives tried (HeadedAt layout))
    (givesMore: ∀ (longer: Expr) => HeadedAt layout longer
      → Gives (() => suffixesFrom more self layout longer) (HeadedAt layout)):
    Gives (() => suffixesAfter more self layout target (Parse.optional tried)) (HeadedAt layout) :=
  givesThen
    (() => Parse.optional tried)
    (suffixesAfter more self layout target)
    (Perhaps (HeadedAt layout))
    (HeadedAt layout)
    (givesOptional tried (HeadedAt layout) givesTried)
    (longer found =>
      match longer, found with
        | Some longer, found => givesMore longer found
        | None, found => givesDone target (HeadedAt layout) headed)

theorem givesHeadedSuffixes ∀ (self: Layout → {Parse (Parse.Located Token)} Expr) (layout: Layout)
    (nested: ∀ (inner: Layout) => Gives (() => self inner) (HeadedAt inner))
    (fuel: Nat) (target: Expr)
    (headed: HeadedAt layout target):
    Gives (() => suffixesFrom fuel self layout target) (HeadedAt layout) :=
  match fuel with
    | Zero => Parse.readsInOfRuns (total state value after fine honest h =>
      match e: state.at.rest with
        | [] => givesHeadedStop layout target headed state.at fine total state value after rfl honest h
        | [token, ..later] =>
          match allowed: layout.allows token with
            | False => givesHeadedStop layout target headed state.at fine total state value after rfl honest h
            | True =>
              match kind: token.value.kind with
                | Sign OpenParen =>
                  givesHeadedStop layout target headed state.at fine total state value after rfl honest h
                | Sign Dot => givesHeadedStop layout target headed state.at fine total state value after rfl honest h
                | Sign CloseParen =>
                  givesHeadedStop layout target headed state.at fine total state value after rfl honest h
                | Sign OpenSquare =>
                  givesHeadedStop layout target headed state.at fine total state value after rfl honest h
                | Sign CloseSquare =>
                  givesHeadedStop layout target headed state.at fine total state value after rfl honest h
                | Sign Comma => givesHeadedStop layout target headed state.at fine total state value after rfl honest h
                | Sign Defines =>
                  givesHeadedStop layout target headed state.at fine total state value after rfl honest h
                | Name text => givesHeadedStop layout target headed state.at fine total state value after rfl honest h
                | Number digits =>
                  givesHeadedStop layout target headed state.at fine total state value after rfl honest h
                | Str written => givesHeadedStop layout target headed state.at fine total state value after rfl honest h
                | Reserved keyword =>
                  givesHeadedStop layout target headed state.at fine total state value after rfl honest h
                | Op operator => givesHeadedStop layout target headed state.at fine total state value after rfl honest h
                | Stray text => givesHeadedStop layout target headed state.at fine total state value after rfl honest h)
    | Succ more => Parse.readsInOfRuns (total state value after fine honest h =>
      match e: state.at.rest with
        | [] => givesHeadedStop layout target headed state.at fine total state value after rfl honest h
        | [token, ..later] =>
          match allowed: layout.allows token with
            | False => givesHeadedStop layout target headed state.at fine total state value after rfl honest h
            | True =>
              match kind: token.value.kind with
                | Sign OpenParen =>
                  givesHeadedSuffixesAfter self layout more target
                    (() => callAfter self target (layout.comments token))
                    headed
                    (givesHeadedCall self (bracketedOf layout) target (layout.comments token) nested headed)
                    (longer longerHeaded => givesHeadedSuffixes self layout nested more longer longerHeaded)
                    state.at
                    fine
                    total
                    state
                    value
                    after
                    rfl
                    honest
                    h
                | Sign Dot =>
                  givesHeadedSuffixesAfter self layout more target
                    (() => fieldAfter layout target (layout.comments token))
                    headed
                    (givesHeadedField (bracketedOf layout) layout target (layout.comments token) headed)
                    (longer longerHeaded => givesHeadedSuffixes self layout nested more longer longerHeaded)
                    state.at
                    fine
                    total
                    state
                    value
                    after
                    rfl
                    honest
                    h
                | Sign CloseParen =>
                  givesHeadedStop layout target headed state.at fine total state value after rfl honest h
                | Sign OpenSquare =>
                  givesHeadedStop layout target headed state.at fine total state value after rfl honest h
                | Sign CloseSquare =>
                  givesHeadedStop layout target headed state.at fine total state value after rfl honest h
                | Sign Comma => givesHeadedStop layout target headed state.at fine total state value after rfl honest h
                | Sign Defines =>
                  givesHeadedStop layout target headed state.at fine total state value after rfl honest h
                | Name text => givesHeadedStop layout target headed state.at fine total state value after rfl honest h
                | Number digits =>
                  givesHeadedStop layout target headed state.at fine total state value after rfl honest h
                | Str written => givesHeadedStop layout target headed state.at fine total state value after rfl honest h
                | Reserved keyword =>
                  givesHeadedStop layout target headed state.at fine total state value after rfl honest h
                | Op operator => givesHeadedStop layout target headed state.at fine total state value after rfl honest h
                | Stray text => givesHeadedStop layout target headed state.at fine total state value after rfl honest h)

theorem givesHeadedPostfix ∀ (self: Layout → {Parse (Parse.Located Token)} Expr) (layout: Layout)
    (nested: ∀ (inner: Layout) => Gives (() => self inner) (HeadedAt inner)):
    Gives (() => postfix self layout) (HeadedAt layout) :=
  givesThen
    (() => Parse.note (Parse.Problem.Expected "an expression"))
    (noted =>
      let first := atom self layout
      suffixesFrom (Parse.mark().left + 1) self layout first)
    (noted => True)
    (HeadedAt layout)
    (Parse.readsWeaken (Parse.readsNote (Parse.Problem.Expected "an expression")) (taken noted none => rfl))
    (noted done =>
      givesThen
        (() => atom self layout)
        (first => suffixesFrom (Parse.mark().left + 1) self layout first)
        (HeadedAt layout)
        (HeadedAt layout)
        (givesHeadedAtom self layout nested)
        (first headed =>
          givesThen
            (() => Parse.mark())
            (at => suffixesFrom (at.left + 1) self layout first)
            (at => True)
            (HeadedAt layout)
            givesMark
            (at marked => givesHeadedSuffixes self layout nested (at.left + 1) first headed)))

theorem givesHeadedNegations ∀ (self: Layout → {Parse (Parse.Located Token)} Expr) (layout: Layout)
    (nested: ∀ (inner: Layout) => Gives (() => self inner) (HeadedAt inner)) (fuel: Nat):
    Gives (() => negationsFrom fuel self layout) (HeadedAt layout) :=
  match fuel with
    | Zero => Parse.readsInOfRuns (total state value after fine honest h =>
      givesHeadedPostfix self layout nested state.at fine total state value after rfl honest h)
    | Succ more => Parse.readsInOfRuns (total state value after fine honest h =>
      match e: state.at.rest with
        | [] => givesHeadedPostfix self layout nested state.at fine total state value after rfl honest h
        | [token, ..later] =>
          match minus: isMinus layout token with
            | False => givesHeadedPostfix self layout nested state.at fine total state value after rfl honest h
            | True =>
              givesThen
                (() => skip())
                (skipped => Negate (layout.comments token) (negationsFrom more self layout))
                (skipped => True)
                (HeadedAt layout)
                givesSkip
                (skipped done =>
                  givesThen
                    (() => negationsFrom more self layout)
                    (inner => Negate (layout.comments token) inner)
                    (HeadedAt layout)
                    (HeadedAt layout)
                    (givesHeadedNegations self layout nested more)
                    (inner headed => givesDone (Negate (layout.comments token) inner) (HeadedAt layout) headed))
                state.at
                fine
                total
                state
                value
                after
                rfl
                honest
                h)

theorem givesHeadedOperand ∀ (self: Layout → {Parse (Parse.Located Token)} Expr) (layout: Layout)
    (nested: ∀ (inner: Layout) => Gives (() => self inner) (HeadedAt inner)):
    Gives (() => operand self layout) (HeadedAt layout) :=
  givesThen
    (() => Parse.mark())
    (at => negationsFrom (at.left + 1) self layout)
    (at => True)
    (HeadedAt layout)
    givesMark
    (at marked => givesHeadedNegations self layout nested (at.left + 1))

-- Operator chains.

theorem headedStep ∀ (layout: Layout) (lowest highest level: Nat) (associativity: Parse.Associativity)
    (combine: Expr → Expr → Expr) (item: Parse.Located Token) (left right: Expr)
    (found: Parse.operatorFrom item 0 (operatorLevels layout) = Some (level, associativity, combine))
    (above: lowest ≤ level)
    (below: level ≤ highest)
    (leftHeaded: HeadedAt layout left)
    (rightHeaded: HeadedAt layout right):
    HeadedAt layout (combine left right) :=
  let shape := operatorShape layout item
  let known := rewrite found at shape in shape
  match known with
    | Witness operator (Witness comments (Both isBinary others)) => rewrite isBinary in Both leftHeaded rightHeaded

theorem givesHeadedChain ∀ (self: Layout → {Parse (Parse.Located Token)} Expr) (layout: Layout)
    (nested: ∀ (inner: Layout) => Gives (() => self inner) (HeadedAt inner)):
    Gives (() => Parse.operators "an operator" (operatorLevels layout) (() => operand self layout)) (HeadedAt layout) :=
  Parse.readsWeaken
    (Parse.readsOperators "an operator"
      (operatorLevels layout)
      (() => operand self layout)
      (HeadedAt layout)
      (lowest expr => HeadedAt layout expr)
      (lowest highest expr => HeadedAt layout expr)
      (givesHeadedOperand self layout nested)
      (lowest highest value headed => headed)
      (lowest highest value headed => headed)
      (headedStep layout))
    (taken value headed => headed)

-- Bodies and blocks.

theorem givesHeadedBare ∀ (self: Layout → {Parse (Parse.Located Token)} Expr) (layout: Layout)
    (nested: ∀ (inner: Layout) => Gives (() => self inner) (HeadedAt inner)):
    Gives (() => bareStatement self layout) (BareHeaded (bracketedOf layout)) :=
  givesThen
    (() => self layout)
    (value => Bare (layout.headed value))
    (HeadedAt layout)
    (BareHeaded (bracketedOf layout))
    (nested layout)
    (value headed => givesDone _ (BareHeaded (bracketedOf layout)) (headedBare layout value headed))

theorem givesHeadedInline ∀ (self: Layout → {Parse (Parse.Located Token)} Expr) (layout: Layout)
    (nested: ∀ (inner: Layout) => Gives (() => self inner) (HeadedAt inner)):
    Gives (() => inlineBody self layout) (HeadedBodyAt layout) :=
  givesThen
    (() => bareStatement self layout)
    (line => { statements = [{ blankBefore = False, line }] })
    (BareHeaded (bracketedOf layout))
    (HeadedBodyAt layout)
    (givesHeadedBare self layout nested)
    (line found =>
      match line, found with
        | Bare value, Both headed isBare =>
          givesDone _ (HeadedBodyAt layout) (Both (Both headed rfl) (Both rfl (inside => rfl)))
        | Let letComments name nameComments equals inner, Both headed never => Void.exfalso (Bool.falseNotTrue never)
        | StatementNote comment, Both headed never => Void.exfalso (Bool.falseNotTrue never))

theorem headedLinesAppend ∀ (bracketed: Bool) (front back: List (Spaced Statement))
    (frontHeaded: HeadedLines bracketed front)
    (backHeaded: HeadedLines bracketed back):
    HeadedLines bracketed (front ++ back) :=
  match front, frontHeaded with
    | [], frontHeaded => backHeaded
    | [{ blankBefore, line }, ..rest], Both lineHeaded restHeaded =>
      Both lineHeaded (headedLinesAppend bracketed rest back restHeaded backHeaded)

theorem headedNotes ∀ (trivia: List Trivia) (found: (List (Spaced Statement), Bool))
    (headed: HeadedLines False found.fst):
    HeadedLines False (trivia.foldLeft found (noteStep StatementNote)).fst :=
  match trivia with
    | [] => headed
    | [BlankLine, ..rest] => headedNotes rest (noteStep StatementNote found BlankLine) headed
    | [OwnLine comment, ..rest] =>
      headedNotes rest
        (noteStep StatementNote found (OwnLine comment))
        (headedLinesAppend False found.fst
          [{ blankBefore = found.snd, line = StatementNote comment }]
          headed
          (Both rfl rfl))

--| A statement's lines, the notes above it and itself.
theorem headedNoted ∀ (above: List Trivia) (line: Statement)
    (headed: HeadedStatement False line):
    HeadedLines False (notedStatement above line) :=
  let notesHeaded: HeadedLines False (spacedNotes StatementNote above).fst := headedNotes above ([], False) rfl
  match found: spacedNotes StatementNote above with
    | (notes, blankBefore) => headedLinesAppend False notes [{ blankBefore, line }] notesHeaded (Both headed rfl)

theorem headedWithoutFirstBlank ∀ (lines: List (Spaced Statement))
    (headed: HeadedLines False lines):
    HeadedLines False (withoutFirstBlank lines) :=
  match lines, headed with
    | [], headed => rfl
    | [{ blankBefore, line }, ..rest], Both lineHeaded restHeaded => Both lineHeaded restHeaded

--| `withoutFirstBlank` leaves no blank line above the first line.
theorem unspacedWithout ∀ (lines: List (Spaced a)): Unspaced (withoutFirstBlank lines) := match lines with
  | [] => rfl
  | [{ blankBefore, line }, ..rest] => rfl

def AllHeaded: List (List (Spaced Statement)) → Prop
  | [] => True
  | [first, ..rest] => HeadedLines False first ∧ AllHeaded rest

theorem eachHeaded ∀ (values: List (List (Spaced Statement))) (taken: List (Parse.Located Token))
    (each: Parse.Each (read lines => HeadedLines False lines) taken values):
    AllHeaded values :=
  match values, each with
    | [], each => rfl
    | [first, ..rest], Witness firstRead (Witness restRead (Both split (Both holds more))) =>
      Both holds (eachHeaded rest restRead more)

theorem headedConcat ∀ (groups: List (List (Spaced Statement)))
    (all: AllHeaded groups):
    HeadedLines False groups.concat :=
  match groups, all with
    | [], all => rfl
    | [first, ..rest], Both firstHeaded restHeaded =>
      headedLinesAppend False first rest.concat firstHeaded (headedConcat rest restHeaded)

--| A statement's line at the statement's own layout: a `let` takes its
--| keyword's comments at the statement's start, where there are none
--| above.
theorem givesHeadedStatementLine ∀ (self: Layout → {Parse (Parse.Located Token)} Expr)
    (nested: ∀ (inner: Layout) => Gives (() => self inner) (HeadedAt inner)) (fuel: Nat)
    (givesBody: ∀ (inner: Layout) => Gives (() => bodyFuel fuel self inner) (HeadedBodyAt inner))
    (column start: Nat) (first: Parse.Located Token) (kind: Kind)
    (noAbove: ((InStatement column start).comments first).above = []):
    Gives (() => statementLine fuel self (InStatement column start) first kind) (HeadedStatement False) :=
  let bare: Gives (() => bareStatement self (InStatement column start)) (HeadedStatement False) :=
    givesWeaken
      (() => bareStatement self (InStatement column start))
      (BareHeaded False)
      (HeadedStatement False)
      (givesHeadedBare self (InStatement column start) nested)
      (line found => found.left)
  match kind with
    | Reserved LetKeyword => Parse.readsThen givesSkip (skipRead skipped done =>
      Parse.readsThen (givesName (InStatement column start)) (nameRead pair named =>
        match pair with
          | (bound, nameComments) =>
            givesThen
              (() => sign (InStatement column start) "'='" Defines)
              (equals =>
                Let
                  ((InStatement column start).comments first)
                  bound
                  nameComments
                  equals
                  (bodyFuel fuel self (InStatement column start)))
              (equals => True)
              (HeadedStatement False)
              (givesSign (InStatement column start) "'='" Defines)
              (equals signed =>
                givesThen
                  (() => bodyFuel fuel self (InStatement column start))
                  (inner => Let ((InStatement column start).comments first) bound nameComments equals inner)
                  (HeadedBody False)
                  (HeadedStatement False)
                  (givesBody (InStatement column start))
                  (inner headed => givesDone _ (HeadedStatement False) (Both noAbove headed)))))
    | Reserved FnKeyword => bare
    | Reserved IfKeyword => bare
    | Reserved ThenKeyword => bare
    | Reserved ElseKeyword => bare
    | Name text => bare
    | Number digits => bare
    | Str written => bare
    | Sign punctuation => bare
    | Op operator => bare
    | Stray text => bare

theorem givesHeadedStatement ∀ (self: Layout → {Parse (Parse.Located Token)} Expr)
    (nested: ∀ (inner: Layout) => Gives (() => self inner) (HeadedAt inner)) (fuel: Nat)
    (givesBody: ∀ (inner: Layout) => Gives (() => bodyFuel fuel self inner) (HeadedBodyAt inner)) (column: Nat):
    Gives (() => statement fuel self column) (HeadedLines False) :=
  Parse.readsInOfRuns (total state value after fine honest h =>
    match e: state.at.rest with
      | [first, ..later] =>
        match starts: first.value.startsLine && first.value.column == column with
          | True =>
            givesThen
              (() => statementLine fuel self (InStatement column first.offset) first first.value.kind)
              (line => notedStatement first.value.above line)
              (HeadedStatement False)
              (HeadedLines False)
              (givesHeadedStatementLine self nested fuel givesBody column first.offset first first.value.kind
                (startAbove column first))
              (line headed => givesDone _ (HeadedLines False) (headedNoted first.value.above line headed))
              state.at
              fine
              total
              state
              value
              after
              rfl
              honest
              h)

theorem givesHeadedBlock ∀ (self: Layout → {Parse (Parse.Located Token)} Expr)
    (nested: ∀ (inner: Layout) => Gives (() => self inner) (HeadedAt inner)) (fuel: Nat)
    (givesBody: ∀ (inner: Layout) => Gives (() => bodyFuel fuel self inner) (HeadedBodyAt inner)) (column: Nat):
    Gives (() => block fuel self column) (HeadedBody False) :=
  givesThen
    (() => Parse.many1 (() => statement fuel self column))
    (lines => { statements = lines.toList.concat |> withoutFirstBlank })
    (lines => AllHeaded lines.toList)
    (HeadedBody False)
    (Parse.readsWeaken
      (Parse.readsMany1
        (() => statement fuel self column)
        (read lines => HeadedLines False lines)
        (givesHeadedStatement self nested fuel givesBody column))
      (taken lines each => eachHeaded lines.toList taken each))
    (lines all =>
      givesDone _
        (HeadedBody False)
        (Both
          (headedWithoutFirstBlank lines.toList.concat (headedConcat lines.toList all))
          (Both (unspacedWithout lines.toList.concat) (never => Void.exfalso (Bool.falseNotTrue never)))))

theorem givesHeadedBodyFuel ∀ (self: Layout → {Parse (Parse.Located Token)} Expr)
    (nested: ∀ (inner: Layout) => Gives (() => self inner) (HeadedAt inner))
    (fuel: Nat) (layout: Layout):
    Gives (() => bodyFuel fuel self layout) (HeadedBodyAt layout) :=
  match fuel with
    | Zero => Parse.readsInOfRuns (total state value after fine honest h => Void.exfalso (Result.errNotOk h))
    | Succ more => Parse.readsInOfRuns (total state value after fine honest h =>
      match layout with
        | InBrackets => givesHeadedInline self InBrackets nested state.at fine total state value after rfl honest h
        | InStatement column start =>
          match e: state.at.rest with
            | [] =>
              givesHeadedInline self
                (InStatement column start)
                nested
                state.at
                fine
                total
                state
                value
                after
                rfl
                honest
                h
            | [token, ..later] =>
              match deeper: token.value.startsLine && token.value.column > column with
                | False =>
                  givesHeadedInline self
                    (InStatement column start)
                    nested
                    state.at
                    fine
                    total
                    state
                    value
                    after
                    rfl
                    honest
                    h
                | True =>
                  givesHeadedBlock self nested more
                    (inner => givesHeadedBodyFuel self nested more inner)
                    token.value.column
                    state.at
                    fine
                    total
                    state
                    value
                    after
                    rfl
                    honest
                    h)

theorem givesHeadedBody ∀ (self: Layout → {Parse (Parse.Located Token)} Expr) (layout: Layout)
    (nested: ∀ (inner: Layout) => Gives (() => self inner) (HeadedAt inner)):
    Gives (() => body self layout) (HeadedBodyAt layout) :=
  givesThen
    (() => Parse.mark())
    (at => bodyFuel (at.left + 1) self layout)
    (at => True)
    (HeadedBodyAt layout)
    givesMark
    (at marked => givesHeadedBodyFuel self nested (at.left + 1) layout)

-- `if`, and the expression parser.

theorem givesHeadedExpressionRule ∀ (self: Layout → {Parse (Parse.Located Token)} Expr) (layout: Layout)
    (nested: ∀ (inner: Layout) => Gives (() => self inner) (HeadedAt inner)):
    Gives (() => expressionRule self layout) (HeadedAt layout) :=
  Parse.readsInOfRuns (total state value after fine honest h =>
    match e: state.at.rest with
      | [] => givesHeadedChain self layout nested state.at fine total state value after rfl honest h
      | [token, ..later] =>
        match found: isIf layout token with
          | False => givesHeadedChain self layout nested state.at fine total state value after rfl honest h
          | True =>
            givesThen
              (() => skip())
              (skipped =>
                let condition := self layout
                let thenComments := keyword layout ThenKeyword
                let whenTrue := body self layout
                let elseComments := elseKeyword layout
                let whenFalse := body self layout
                If (layout.comments token) condition thenComments whenTrue elseComments whenFalse)
              (skipped => True)
              (HeadedAt layout)
              givesSkip
              (skipped done =>
                givesThen
                  (() => self layout)
                  (condition =>
                    let thenComments := keyword layout ThenKeyword
                    let whenTrue := body self layout
                    let elseComments := elseKeyword layout
                    let whenFalse := body self layout
                    If (layout.comments token) condition thenComments whenTrue elseComments whenFalse)
                  (HeadedAt layout)
                  (HeadedAt layout)
                  (nested layout)
                  (condition conditionHeaded =>
                    givesThen
                      (() => keyword layout ThenKeyword)
                      (thenComments =>
                        let whenTrue := body self layout
                        let elseComments := elseKeyword layout
                        let whenFalse := body self layout
                        If (layout.comments token) condition thenComments whenTrue elseComments whenFalse)
                      (thenComments => True)
                      (HeadedAt layout)
                      (givesKeyword layout ThenKeyword)
                      (thenComments thenRead =>
                        givesThen
                          (() => body self layout)
                          (whenTrue =>
                            let elseComments := elseKeyword layout
                            let whenFalse := body self layout
                            If (layout.comments token) condition thenComments whenTrue elseComments whenFalse)
                          (HeadedBodyAt layout)
                          (HeadedAt layout)
                          (givesHeadedBody self layout nested)
                          (whenTrue trueHeaded =>
                            givesThen
                              (() => elseKeyword layout)
                              (elseComments =>
                                let whenFalse := body self layout
                                If (layout.comments token) condition thenComments whenTrue elseComments whenFalse)
                              (elseComments => True)
                              (HeadedAt layout)
                              (givesElse layout)
                              (elseComments elseRead =>
                                givesThen
                                  (() => body self layout)
                                  (whenFalse =>
                                    If (layout.comments token) condition thenComments whenTrue elseComments whenFalse)
                                  (HeadedBodyAt layout)
                                  (HeadedAt layout)
                                  (givesHeadedBody self layout nested)
                                  (whenFalse falseHeaded =>
                                    givesDone _
                                      (HeadedAt layout)
                                      (Both conditionHeaded (Both trueHeaded falseHeaded))))))))
              state.at
              fine
              total
              state
              value
              after
              rfl
              honest
              h)

--| Every expression the parser gives is `HeadedExpr`, inside brackets or
--| not as its layout is.
theorem givesHeadedExpression ∀ (layout: Layout): Gives (() => expression layout) (HeadedAt layout) :=
  Parse.readsRecursiveWith expressionRule
    (inner taken expr => HeadedAt inner expr)
    (self nested argument => givesHeadedExpressionRule self argument nested)
    layout

-- Declarations and the file.

theorem givesHeadedFunctionLine ∀ (column start: Nat) (first: Parse.Located Token)
    (noAbove: ((InStatement column start).comments first).above = []):
    Gives (() => functionLine (InStatement column start) first) HeadedDeclaration :=
  Parse.readsThen givesSkip (skipRead skipped done =>
    Parse.readsThen (givesName (InStatement column start)) (nameRead pair named =>
      match pair with
        | (declared, nameComments) =>
          givesThen
            (() => sign (InStatement column start) "'('" OpenParen)
            (open =>
              let parameters := parametersOf (Parse.optional parameterList)
              let close := sign InBrackets "')'" CloseParen
              let equals := sign (InStatement column start) "'='" Defines
              Function
                ((InStatement column start).comments first)
                declared
                nameComments
                open
                parameters
                close
                equals
                (body expression (InStatement column start)))
            (open => True)
            HeadedDeclaration
            (givesSign (InStatement column start) "'('" OpenParen)
            (open opened =>
              givesThen
                (() => parametersOf (Parse.optional parameterList))
                (parameters =>
                  let close := sign InBrackets "')'" CloseParen
                  let equals := sign (InStatement column start) "'='" Defines
                  Function
                    ((InStatement column start).comments first)
                    declared
                    nameComments
                    open
                    parameters
                    close
                    equals
                    (body expression (InStatement column start)))
                (parameters => True)
                HeadedDeclaration
                (givesWeaken
                  (() => parametersOf (Parse.optional parameterList))
                  BareLast
                  (parameters => True)
                  givesParameters
                  (parameters bare => rfl))
                (parameters listed =>
                  givesThen
                    (() => sign InBrackets "')'" CloseParen)
                    (close =>
                      let equals := sign (InStatement column start) "'='" Defines
                      Function
                        ((InStatement column start).comments first)
                        declared
                        nameComments
                        open
                        parameters
                        close
                        equals
                        (body expression (InStatement column start)))
                    (close => True)
                    HeadedDeclaration
                    (givesSign InBrackets "')'" CloseParen)
                    (close closed =>
                      givesThen
                        (() => sign (InStatement column start) "'='" Defines)
                        (equals =>
                          Function
                            ((InStatement column start).comments first)
                            declared
                            nameComments
                            open
                            parameters
                            close
                            equals
                            (body expression (InStatement column start)))
                        (equals => True)
                        HeadedDeclaration
                        (givesSign (InStatement column start) "'='" Defines)
                        (equals signed =>
                          givesThen
                            (() => body expression (InStatement column start))
                            (inner =>
                              Function
                                ((InStatement column start).comments first)
                                declared
                                nameComments
                                open
                                parameters
                                close
                                equals
                                inner)
                            (HeadedBody False)
                            HeadedDeclaration
                            (givesHeadedBody expression (InStatement column start) givesHeadedExpression)
                            (inner headed => givesDone _ HeadedDeclaration (Both noAbove headed))))))))

theorem givesHeadedValueLine ∀ (column start: Nat) (first: Parse.Located Token)
    (noAbove: ((InStatement column start).comments first).above = []):
    Gives (() => valueLine (InStatement column start) first) HeadedDeclaration :=
  Parse.readsThen givesSkip (skipRead skipped done =>
    Parse.readsThen (givesName (InStatement column start)) (nameRead pair named =>
      match pair with
        | (declared, nameComments) =>
          givesThen
            (() => sign (InStatement column start) "'='" Defines)
            (equals =>
              Value
                ((InStatement column start).comments first)
                declared
                nameComments
                equals
                (body expression (InStatement column start)))
            (equals => True)
            HeadedDeclaration
            (givesSign (InStatement column start) "'='" Defines)
            (equals signed =>
              givesThen
                (() => body expression (InStatement column start))
                (inner => Value ((InStatement column start).comments first) declared nameComments equals inner)
                (HeadedBody False)
                HeadedDeclaration
                (givesHeadedBody expression (InStatement column start) givesHeadedExpression)
                (inner headed => givesDone _ HeadedDeclaration (Both noAbove headed)))))

theorem givesHeadedDeclarationLine ∀ (column start: Nat) (first: Parse.Located Token)
    (noAbove: ((InStatement column start).comments first).above = []):
    Gives (() => declarationLine (InStatement column start) first) HeadedDeclaration :=
  Parse.readsInOfRuns (total state value after fine honest h =>
    match kind: first.value.kind with
      | Reserved FnKeyword =>
        givesHeadedFunctionLine column start first noAbove state.at fine total state value after rfl honest h
      | Reserved LetKeyword =>
        givesHeadedValueLine column start first noAbove state.at fine total state value after rfl honest h)

theorem headedDeclarationsAppend ∀ (front back: List (Spaced Declaration))
    (frontHeaded: HeadedDeclarations front)
    (backHeaded: HeadedDeclarations back):
    HeadedDeclarations (front ++ back) :=
  match front, frontHeaded with
    | [], frontHeaded => backHeaded
    | [{ blankBefore, line }, ..rest], Both lineHeaded restHeaded =>
      Both lineHeaded (headedDeclarationsAppend rest back restHeaded backHeaded)

theorem headedDeclarationNotes ∀ (trivia: List Trivia) (found: (List (Spaced Declaration), Bool))
    (headed: HeadedDeclarations found.fst):
    HeadedDeclarations (trivia.foldLeft found (noteStep DeclarationNote)).fst :=
  match trivia with
    | [] => headed
    | [BlankLine, ..rest] => headedDeclarationNotes rest (noteStep DeclarationNote found BlankLine) headed
    | [OwnLine comment, ..rest] =>
      headedDeclarationNotes rest
        (noteStep DeclarationNote found (OwnLine comment))
        (headedDeclarationsAppend found.fst
          [{ blankBefore = found.snd, line = DeclarationNote comment }]
          headed
          (Both rfl rfl))

theorem headedNotedDeclaration ∀ (above: List Trivia) (line: Declaration)
    (headed: HeadedDeclaration line):
    HeadedDeclarations (notedDeclaration above line) :=
  let notesHeaded: HeadedDeclarations (spacedNotes DeclarationNote above).fst :=
    headedDeclarationNotes above ([], False) rfl
  match found: spacedNotes DeclarationNote above with
    | (notes, blankBefore) => headedDeclarationsAppend notes [{ blankBefore, line }] notesHeaded (Both headed rfl)

theorem headedDeclarationsWithoutFirstBlank ∀ (lines: List (Spaced Declaration))
    (headed: HeadedDeclarations lines):
    HeadedDeclarations (withoutFirstBlank lines) :=
  match lines, headed with
    | [], headed => rfl
    | [{ blankBefore, line }, ..rest], Both lineHeaded restHeaded => Both lineHeaded restHeaded

def AllHeadedDeclarations: List (List (Spaced Declaration)) → Prop
  | [] => True
  | [first, ..rest] => HeadedDeclarations first ∧ AllHeadedDeclarations rest

theorem eachHeadedDeclarations ∀ (values: List (List (Spaced Declaration))) (taken: List (Parse.Located Token))
    (each: Parse.Each (read lines => HeadedDeclarations lines) taken values):
    AllHeadedDeclarations values :=
  match values, each with
    | [], each => rfl
    | [first, ..rest], Witness firstRead (Witness restRead (Both split (Both holds more))) =>
      Both holds (eachHeadedDeclarations rest restRead more)

theorem headedDeclarationsConcat ∀ (groups: List (List (Spaced Declaration)))
    (all: AllHeadedDeclarations groups):
    HeadedDeclarations groups.concat :=
  match groups, all with
    | [], all => rfl
    | [first, ..rest], Both firstHeaded restHeaded =>
      headedDeclarationsAppend first rest.concat firstHeaded (headedDeclarationsConcat rest restHeaded)

theorem givesHeadedDeclaration: Gives declaration HeadedDeclarations :=
  Parse.readsInOfRuns (total state value after fine honest h =>
    match e: state.at.rest with
      | [first, ..later] =>
        match starts: first.value.startsLine && first.value.column == 0 with
          | True =>
            givesThen
              (() => declarationLine (InStatement 0 first.offset) first)
              (parsed => notedDeclaration first.value.above parsed)
              HeadedDeclaration
              HeadedDeclarations
              (givesHeadedDeclarationLine 0 first.offset first (startAbove 0 first))
              (parsed headed => givesDone _ HeadedDeclarations (headedNotedDeclaration first.value.above parsed headed))
              state.at
              fine
              total
              state
              value
              after
              rfl
              honest
              h)

theorem headedFileOf ∀ (declarations: List (Spaced Declaration)) (endTrivia: List Trivia)
    (headed: HeadedDeclarations declarations):
    HeadedFile (fileOf declarations endTrivia) :=
  let notesHeaded: HeadedDeclarations (spacedNotes DeclarationNote endTrivia).fst :=
    headedDeclarationNotes endTrivia ([], False) rfl
  match found: spacedNotes DeclarationNote endTrivia with
    | (endNotes, blank) =>
      Both
        (headedDeclarationsWithoutFirstBlank
          (declarations ++ endNotes)
          (headedDeclarationsAppend declarations endNotes headed notesHeaded))
        (unspacedWithout (declarations ++ endNotes))

theorem givesHeadedFileEnd ∀ (declarations: List (Spaced Declaration)) (endTrivia: List Trivia)
    (headed: HeadedDeclarations declarations):
    Gives (() => fileEnd declarations endTrivia) HeadedFile :=
  Parse.readsInOfRuns (total state value after fine honest h =>
    match e: state.at.rest with
      | [] =>
        givesDone
          (fileOf declarations endTrivia)
          HeadedFile
          (headedFileOf declarations endTrivia headed)
          state.at
          fine
          total
          state
          value
          after
          rfl
          honest
          h
      | [token, ..later] =>
        match indented: token.value.startsLine && token.value.column > 0 with
          | False =>
            givesDone
              (fileOf declarations endTrivia)
              HeadedFile
              (headedFileOf declarations endTrivia headed)
              state.at
              fine
              total
              state
              value
              after
              rfl
              honest
              h)

theorem givesHeadedSourceFile ∀ (endTrivia: List Trivia): Gives (() => sourceFile endTrivia) HeadedFile :=
  givesThen
    (() => Parse.many declaration)
    (found => fileEnd found.concat endTrivia)
    AllHeadedDeclarations
    HeadedFile
    (Parse.readsWeaken
      (Parse.readsMany declaration (read lines => HeadedDeclarations lines) givesHeadedDeclaration)
      (taken found each => eachHeadedDeclarations found taken each))
    (found all => givesHeadedFileEnd found.concat endTrivia (headedDeclarationsConcat found all))

--| What the parser guarantees of where comments and blocks are: in
--| every file `parse` gives, whatever the source, outside brackets no
--| statement's, declaration's or one-expression body's first token holds
--| comments above it in the tree (above a statement or declaration they
--| are the list's comment lines); inside brackets every body is one
--| expression; and no body, and not the file, keeps a blank line above
--| its first line. So the spelling theorems' `Headed` hypotheses hold of
--| every parsed tree, with no check at run time.
theorem parseHeaded ∀ (source: Text) (file: SourceFile) (parsed: parse source = Ok file): HeadedFile file :=
  match lexed: lex source with
    | Ok tokens =>
      match whole: Parse.whole tokens.tokens (() => sourceFile tokens.endTrivia) with
        | Ok found =>
          let same: found = file := Result.okInjective parsed
          rewrite <- same in
            Parse.wholeReads tokens.tokens
              (() => sourceFile tokens.endTrivia)
              (taken value => HeadedFile value)
              found
              (givesHeadedSourceFile tokens.endTrivia)
              whole
