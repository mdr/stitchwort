--| The parsers outside slice 1 give `Out` (their tree is outside the slice), proved for the tiers of `Outside` that need
--| only the walks of `Syntax.ParseWalk` and `ParseWalkLadder`: the atoms' rests, lists and the rest of what an atom
--| can be. It also has the small facts the `def` frame and the declarations share (`givesFixedFrom`, the
--| qualified-name and attribute parsers, `NameOk`, `BodyOk`), which the later files all read.

namespace Syntax.ParseWalkOutside
import Std (Bool, DecEq, Eq, List, Nat, Option, Pair, Parse, Result, Text)
import Syntax (..)
import Fmt (..)
import Syntax.LexProofs (..)
import Syntax.ParseProofs (..)
import Syntax.ParseWalk (..)
import Syntax.ParseWalkLadder (..)
import Fmt.Grammar1 (..)
import Fmt.Kinds (..)

-- What the `def` frame and the declarations share, and the parsers they read the attributes and names with.

--| A definition's name is a name, of the lower-case kind or the upper-case one (`def Foo: Nat := 1` is in slice 1).
def NameOk (name: Word): Prop := name.lexesAs Lower = True ∨ name.lexesAs Upper = True

def BodyOk: DefBody → Prop
  | Assigned colonEq value => Parsed 1 value
  | other => True

theorem givesFixedFrom: Parse.Gives GoodItems (() => fixedFrom()) (comments => True) := byWalking [givesBump]

theorem givesLowerQualified ∀ (modes: Modes) (what: Text):
    Parse.Gives GoodItems (() => modes.lowerQualified what) NameOk :=
  readsInPeeked modes
    (seen => modes.lowerQualifiedOn what seen) _
    (start fine stops => givesFailName modes what start fine)
    (start item later shape fine stopped =>
      match took: isSome Lower (Some item.kind) with
        | False => givesFailName modes what start fine
        | True => Parse.readsAtWeaken (readsAtBump shape) (read word (single, same) =>
          rewrite same then
            Inl
              (wordLexesAs item.leaf.word Lower
                (rewrite <- DecEq.sound took then
                  lexesAsSpells item.kind item.text
                    (goodHead fine shape (rewrite DecEq.sound took))
                    (mayFollowEnd item.kind item.text)))))

theorem givesLowerQualifiedAny ∀ (modes: Modes) (what: Text):
    Parse.Gives GoodItems (() => modes.lowerQualified what) (word => True) :=
  Parse.givesWeaken (givesLowerQualified modes what) (found ok => byComputing)

theorem givesAttributePart ∀ (modes: Modes) (dot: Bool):
    Parse.Gives GoodItems (() => attributePart modes dot) (Parse.Perhaps (found => True)) :=
  byWalking [givesFixedFrom, givesLowerQualifiedAny]

theorem givesAttributeParts ∀ (modes: Modes): Parse.Gives GoodItems (() => attributeParts modes) (found => True) :=
  Parse.givesWeaken
    (Parse.givesLoop (Parse.givesAfter0 (reads0At modes Dot) (dot => givesAttributePart modes dot)))
    (found ok => byComputing)

theorem givesAttributeArgument ∀ (modes: Modes):
    Parse.Gives GoodItems (() => attributeArgument modes) (found => True) :=
  Parse.givesAfter0 (reads0Peek modes) (seen =>
    match isSome Str seen with
      | True => Parse.givesThen givesBump (taken _ => Parse.givesDone byComputing)
      | False =>
        match isSome StrStart seen with
          | True => Parse.readsFatal
          | False => Parse.givesDone byComputing)

theorem givesAttributeItems ∀ (fuel: Nat) (modes: Modes) (found: List Attribute):
    Parse.Gives GoodItems (() => attributeItems fuel modes found) (pair => True) :=
  match fuel with
    | Zero => Parse.givesDone byComputing
    | Succ more => Parse.givesAfter0 (reads0At modes RBracket) (closed =>
      match closed && !found.isEmpty with
        | True => Parse.givesDone byComputing
        | False => Parse.givesThen (givesLowerQualifiedAny modes "an attribute's name, such as `js.name`") (name _ =>
          Parse.givesThen (givesAttributeParts modes) (parts _ =>
            Parse.givesThen (givesAttributeArgument modes) (written _ =>
              Parse.givesAfter0 [p := () => modes.at Comma] (reads0At modes Comma) (comma =>
                match comma with
                  | True => Parse.givesThen givesBump (gone _ =>
                    givesAttributeItems more modes [{ name, parts, argument = written }, ..found])
                  | False => Parse.givesDone byComputing)))))

theorem givesAttributeGroup ∀ (modes: Modes):
    Parse.Gives GoodItems (() => attributeGroup modes) (Parse.Perhaps (found => True)) :=
  Parse.givesThen givesFixedFrom (at _ =>
    Parse.givesThen (givesExpectFixed modes LBracket "`[`") (open _ =>
      Parse.givesThen Parse.givesMark (here _ =>
        Parse.givesThen (givesAttributeItems (here.left + 1) modes []) (pair _ =>
          match pair with
            | (items, trailingComma) =>
              Parse.givesThen (givesExpectFixed modes RBracket "`,` or `]` after the attribute") (close _ =>
                Parse.givesDone byComputing)))))

theorem givesAttributesOf ∀ (modes: Modes): Parse.Gives GoodItems (() => attributesOf modes) (found => True) :=
  Parse.givesWeaken
    (Parse.givesLoop
      (Parse.givesAfter0 (reads0At modes At) (found =>
        match found with
          | True => givesAttributeGroup modes
          | False => Parse.givesDone byComputing)))
    (found ok => byComputing)

-- The parsers outside slice 1, proved.

theorem givesSemiAfter ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (value: Expr) (semicolon: Word)
    (nested: Nested self) (seen: Option Tok):
    Parse.Gives GoodItems (() => semiAfter self modes value semicolon seen) Out :=
  match seen with
    | None | Some RParen | Some RBracket | Some RBrace | Some Comma => Parse.readsFatal
    | Some other => Parse.givesThen (nested { modes, level = LevelFull }) (tail parsed => Parse.givesDone byComputing)

theorem givesSemi ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (value: Expr)
    (nested: Nested self):
    Parse.Gives GoodItems (() => semiExpr self modes value) Out :=
  byWalking [givesBump, givesSemiAfter]

--| `expect` gives the word of a token of any kind it was asked for.
theorem givesExpectAny ∀ (modes: Modes) (wanted: Tok) (what: Text):
    Parse.Gives GoodItems (() => modes.expect wanted what) (word => True) :=
  readsInPeeked modes
    (seen => modes.expectOn wanted what seen) _
    (start fine stops => givesFail modes what start fine)
    (start item later shape fine stopped =>
      match took: isSome wanted (Some item.kind) with
        | False => givesFail modes what start fine
        | True => Parse.readsAtWeaken (readsAtBump shape) (read word (single, same) => byComputing))

theorem givesAnnotatedEnd ∀ (inner: Modes) (open: Word) (first: Expr) (colon: Word) (annotation: Expr) (comma: Bool):
    Parse.Gives GoodItems (() => annotatedEnd inner open first colon annotation comma) Out :=
  byWalking [givesExpectAny]

theorem givesAnnotated ∀ (self: Goal → {Parse Item} Expr) (inner: Modes) (open: Word) (first: Expr)
    (nested: Nested self):
    Parse.Gives GoodItems (() => annotated self inner open first) Out :=
  byWalking [givesBump, givesAnnotatedEnd]

theorem givesLower ∀ (modes: Modes) (what: Text): Parse.Gives GoodItems (() => modes.lower what) (word => True) :=
  Parse.givesAfter0 reads0Left (items =>
    match items with
      | [item, ..rest] =>
        match named: item.kind == Lower && !modes.stops item with
          | True =>
            match qualified: isQualified item with
              | True => Parse.readsFatal
              | False => givesBump
          | False => givesFailName modes what
      | [] => givesFailName modes what)

theorem givesNamedClose ∀ (inner: Modes) (open name colonEq: Word) (value: Expr) (closer: Tok) (closeText: Text):
    Parse.Gives GoodItems (() => namedClose inner open name colonEq value closer closeText) Out :=
  byWalking [givesExpectAny]

theorem givesNamedColon ∀ (self: Goal → {Parse Item} Expr) (inner: Modes) (open name: Word)
    (closer: Tok) (closeText: Text)
    (nested: Nested self):
    Parse.Gives GoodItems (() => namedColon self inner open name closer closeText) Out :=
  byWalking [givesBump, givesNamedClose]

theorem givesNamedHead ∀ (self: Goal → {Parse Item} Expr) (inner: Modes) (open: Word) (closer: Tok) (closeText: Text)
    (nested: Nested self) (clause: Bool):
    Parse.Gives GoodItems (() => namedHead self inner open closer closeText clause) Out :=
  match clause with
    | True => Parse.givesThen givesBump (name _ => givesNamedColon self inner open name closer closeText nested)
    | False => Parse.givesThen (givesLower inner "a name") (name _ =>
      givesNamedColon self inner open name closer closeText nested)

theorem givesNamedArgument ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (closer: Tok) (closeText: Text)
    (nested: Nested self):
    Parse.Gives GoodItems (() => namedArgument self modes closer closeText) Out :=
  byWalking [givesBump, givesNamedHead]

--| A gap is an error, which gives anything.
theorem givesGap ∀ (modes: Modes) (message: Text) [holds: a → Prop]:
    Parse.Gives GoodItems (() => modes.gap message) holds :=
  Parse.givesAfter0 reads0Left (items =>
    match blockEnd modes.lines items.head with
      | Some ending => Parse.readsFatal
      | None => Parse.readsFatal)

theorem reads0RanOutAtLine ∀ (modes: Modes): Reads0 (() => ranOutAtLine modes) :=
  Parse.reads0Then (reads0Peek modes) (seen =>
    Parse.reads0Then reads0Left (items => Parse.reads0Done (ranOutOn modes seen items)))

theorem givesAtomGap ∀ (modes: Modes) (ran: Bool): Parse.Gives GoodItems (() => atomGap modes ran) Out := match ran with
  | True => givesGap modes ranOutLine
  | False => Parse.givesThen (givesUnexpected modes "an expression") (message _ => givesGap modes message)

theorem givesAtomNamed ∀ (modes: Modes) (second: Option Tok):
    Parse.Gives GoodItems (() => atomNamed modes second) Out :=
  byWalking [givesFailName, givesFail]

theorem givesAtomMissing ∀ (self: Goal → {Parse Item} Expr) (modes: Modes):
    Parse.Gives GoodItems (() => atomMissing self modes) Out :=
  Parse.givesAfter0 (reads0Peek modes) (seen =>
    match modes.recover && seen.isNone with
      | True =>
        Parse.givesAfter0 [p := () => ranOutAtLine modes] (reads0RanOutAtLine modes) (ran => givesAtomGap modes ran)
      | False =>
        Parse.givesAfter0 [p := () => modes.peekAt 1] (reads0PeekAt modes 1) (second => givesAtomNamed modes second))

theorem givesNamedBinder ∀ (modes: Modes): Parse.Gives GoodItems (() => namedBinder modes) (found => True) :=
  Parse.givesAfter0 (reads0At modes Lower) (lower =>
    Parse.givesAfter0 (reads0PeekAt modes 1) (second =>
      match lower && isSome Colon second with
        | True => Parse.givesThen (givesLower modes "a name") (name _ =>
          Parse.givesThen givesBump (colon _ => Parse.givesDone byComputing))
        | False => Parse.givesDone byComputing))

theorem givesExpectKeyword ∀ (modes: Modes) (wanted: Tok) (what: Text) (indent: Nat):
    Parse.Gives GoodItems (() => modes.expectKeyword wanted what indent) (word => True) :=
  Parse.givesAfter0 (reads0Peek modes) (seen =>
    Parse.givesAfter0 reads0Left (items =>
      match seen, items with
        | None, [item, ..rest] =>
          match line: item.kind == wanted && item.leaf.token.lineStart && item.leaf.token.column >= indent with
            | True => givesBump
            | False => givesExpectAny modes wanted what
        | None, [] => givesExpectAny modes wanted what
        | Some kind, others => givesExpectAny modes wanted what))

theorem givesIf ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (indent: Nat) (keyword: Word)
    (nested: Nested self):
    Parse.Gives GoodItems (() => ifExpr self modes indent keyword) Out :=
  byWalking [givesNamedBinder, givesExpectKeyword]

theorem givesIfKeyword ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self):
    Parse.Gives GoodItems (() => ifKeyword self modes) Out :=
  Parse.givesAfter0 reads0HeadIndent (indent =>
    Parse.givesThen givesBump (keyword _ => givesIf self modes indent keyword nested))

--| What `self` gives at some goal, nothing is known of.
theorem givesSelfAny ∀ (self: Goal → {Parse Item} Expr)
    (nested: Nested self) (goal: Goal):
    Parse.Gives GoodItems (() => self goal) (expr => True) :=
  Parse.readsWeaken (nested goal) (read found parsed => byComputing)

theorem givesSectionOperand ∀ (self: Goal → {Parse Item} Expr) (inner: Modes) (operatorKind: Tok)
    (nested: Nested self):
    Parse.Gives GoodItems (() => sectionOperand self inner operatorKind) (expr => True) :=
  match operatorKind with
    | Plus => givesSelfAny self nested { modes = inner, level = LevelMultiplicative }
    | Star | Slash | Percent => givesSelfAny self nested { modes = inner, level = LevelUnary }
    | AndAnd => givesSelfAny self nested { modes = inner, level = LevelComparison }
    | OrOr => Parse.givesThen (givesSelfAny self nested { modes = inner, level = LevelComparison }) (first _ =>
      Parse.givesThen
        (Parse.givesWeaken
          [weaker := links => True]
          (Parse.givesLoop
            (givesOperatorStep inner
              (kind => kind == AndAnd)
              (() => self { modes = inner, level = LevelComparison })
              6
              (link => True)
              (chosen value good took parsed => byComputing)
              (nested { modes = inner, level = LevelComparison })))
          (links ok => byComputing))
        (links _ => Parse.givesDone byComputing))
    | IffArrow => givesSelfAny self nested { modes = inner, level = LevelLogic }
    | other => givesSelfAny self nested { modes = inner, level = LevelAppend }

theorem givesOperatorClose ∀ (open operator: Word) (operand: Option Expr):
    Parse.Gives GoodItems (() => operatorClose open operator operand) Out :=
  byWalking [givesBump]

theorem givesOperatorEnd ∀ (inner: Modes) (open operator: Word) (operand: Expr) (closed: Bool):
    Parse.Gives GoodItems (() => operatorEnd inner open operator operand closed) Out :=
  byWalking [givesOperatorClose, givesFail]

theorem givesOperatorHead ∀ (self: Goal → {Parse Item} Expr) (inner: Modes) (open: Word)
    (operatorKind: Tok) (operator: Word)
    (nested: Nested self) (closed: Bool):
    Parse.Gives GoodItems (() => operatorHead self inner open operatorKind operator closed) Out :=
  byWalking [givesOperatorClose, givesSectionOperand, givesOperatorEnd]

theorem givesOperatorFirst ∀ (self: Goal → {Parse Item} Expr) (inner: Modes) (open: Word) (items: List Item)
    (nested: Nested self):
    Parse.Gives GoodItems (() => operatorFirst self inner open items) Out :=
  byWalking [givesBump, givesOperatorHead]

theorem givesOperatorSection ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self):
    Parse.Gives GoodItems (() => operatorSection self modes) Out :=
  byWalking [givesBump, givesOperatorFirst]

theorem givesRightOperand ∀ (self: Goal → {Parse Item} Expr) (inner: Modes) (operatorKind: Tok)
    (nested: Nested self):
    Parse.Gives GoodItems (() => rightOperand self inner operatorKind) (found => True) :=
  match operatorKind with
    | Plus => givesSelfAny self nested { modes = inner, level = LevelMultiplicative }
    | Star | Slash | Percent => givesSelfAny self nested { modes = inner, level = LevelUnary }
    | PlusPlus => givesSelfAny self nested { modes = inner, level = LevelAdditive }
    | AndAnd | OrOr | IffArrow => givesSelfAny self nested { modes = inner, level = LevelComparison }
    | other => givesSelfAny self nested { modes = inner, level = LevelAppend }

theorem givesRightClose ∀ (inner: Modes) (open: Word) (operand: Expr) (operator: Word):
    Parse.Gives GoodItems (() => rightClose inner open operand operator) Out :=
  byWalking [givesExpectAny]

theorem givesRightEnd ∀ (inner: Modes) (open: Word) (inside start: Nat) (operand: Expr) (here: Nat):
    Parse.Gives GoodItems (() => rightEnd inner open inside start operand here) Out :=
  byWalking [givesFail, givesBump, givesRightClose]

theorem givesRightKind ∀ (self: Goal → {Parse Item} Expr) (inner: Modes) (open: Word)
    (inside start: Nat) (items: List Item)
    (nested: Nested self):
    Parse.Gives GoodItems (() => rightKind self inner open inside start items) Out :=
  Parse.givesThen (givesRightOperand self inner _ nested) (operand _ =>
    Parse.givesAfter0 reads0Offset (here => givesRightEnd inner open inside start operand here))

theorem givesRightSection ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (inside: Nat)
    (nested: Nested self):
    Parse.Gives GoodItems (() => rightSection self modes inside) Out :=
  Parse.givesThen givesBump (open _ =>
    Parse.givesAfter0 reads0Offset (start =>
      Parse.givesAfter0 reads0Left (items => givesRightKind self modes.inBrackets open inside start items nested)))

theorem givesCmpIf ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (lhs: Expr) (operator: Word)
    (nested: Nested self):
    Parse.Gives GoodItems (() => cmpIf self modes lhs operator) Out :=
  Parse.givesAfter0 reads0HeadIndent (indent =>
    Parse.givesThen givesBump (keyword _ =>
      Parse.givesThen (givesIf self modes indent keyword nested) (tail out =>
        Parse.givesDone (Bool.andFalseRight lhs.grammar1 tail.grammar1 out))))

theorem givesParenOther ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (second third: Option Tok)
    (nested: Nested self):
    Parse.Gives GoodItems (() => parenOther self modes second third) Out :=
  byWalking [givesBump, givesNamedArgument, givesOperatorSection]

theorem givesRecordFieldAfter ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (name: Word)
    (nested: Nested self) (equalsNext: Bool):
    Parse.Gives GoodItems (() => recordFieldAfter self modes name equalsNext) (found => True) :=
  byWalking [givesBump]

theorem givesRecordField ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self):
    Parse.Gives GoodItems (() => recordField self modes) (found => True) :=
  byWalking [givesLower, givesRecordFieldAfter]

theorem givesRecordEnd ∀ (inner: Modes) (open: Word) (base: Option (Expr, Word)) (pair: (List Expr, Bool)):
    Parse.Gives GoodItems (() => recordEnd inner open base pair) Out :=
  byWalking [givesExpectAny]

theorem givesRecordFields ∀ (self: Goal → {Parse Item} Expr) (inner: Modes) (open: Word) (base: Option (Expr, Word))
    (nested: Nested self):
    Parse.Gives GoodItems (() => recordFields self inner open base) Out :=
  Parse.givesThen (givesRecordField self inner nested) (first _ =>
    Parse.givesThen Parse.givesMark (here _ =>
      Parse.givesThen
        (givesCommaListFrom inner
          (count => inner.at RBrace)
          (() => recordField self inner)
          (found => True)
          (count => givesAt inner RBrace)
          (givesRecordField self inner nested)
          (here.left + 1)
          1
          first
          []
          byComputing
          ())
        (pair _ => givesRecordEnd inner open base pair)))

theorem givesRecordBase ∀ (self: Goal → {Parse Item} Expr) (inner: Modes)
    (nested: Nested self) (literal: Bool):
    Parse.Gives GoodItems (() => recordBase self inner literal) (found => True) :=
  match literal with
    | True => Parse.givesDone byComputing
    | False => Parse.givesThen (nested { modes = inner, level = LevelFull }) (record _ =>
      Parse.givesThen (givesExpectAny inner Pipe "`|` and the fields to update") (bar _ => Parse.givesDone byComputing))

theorem givesRecordBody ∀ (self: Goal → {Parse Item} Expr) (inner: Modes) (open: Word)
    (nested: Nested self) (empty: Bool):
    Parse.Gives GoodItems (() => recordBody self inner open empty) Out :=
  match empty with
    | True => Parse.givesThen givesBump (close _ => Parse.givesDone byComputing)
    | False => Parse.givesAfter0 (reads0At inner Lower) (lower =>
      Parse.givesAfter0 (reads0PeekAt inner 1) (second =>
        Parse.givesThen (givesRecordBase self inner nested (lower && literalSecond second)) (base _ =>
          givesRecordFields self inner open base nested)))

theorem givesRecordExpr ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self):
    Parse.Gives GoodItems (() => recordExpr self modes) Out :=
  byWalking [givesExpectAny, givesRecordBody]

theorem givesExpectFixed ∀ (modes: Modes) (wanted: Tok) (what: Text):
    Parse.Gives GoodItems (() => modes.expectFixed wanted what) (comments => True) :=
  byWalking [givesExpectAny]

theorem givesRowAbilities ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self) (closed pipe: Bool):
    Parse.Gives GoodItems (() => rowAbilities self modes closed pipe) (found => True) :=
  match closed || pipe with
    | True => Parse.givesDone byComputing
    | False => Parse.givesThen (nested { modes, level = LevelApp }) (first _ =>
      Parse.givesThen Parse.givesMark (here _ =>
        Parse.givesThen
          (givesCommaListFrom modes
            (count => False)
            (() => self { modes, level = LevelApp })
            (found => True)
            (count => Parse.givesDone byComputing)
            (givesSelfAny self nested { modes, level = LevelApp })
            (here.left + 1)
            1
            first
            []
            byComputing
            ())
          (pair _ => Parse.givesDone byComputing)))

theorem givesRowPart ∀ (modes: Modes) (pipe: Bool): Parse.Gives GoodItems (() => rowPart modes pipe) (found => True) :=
  byWalking [givesFixedFrom, givesLower]

theorem givesRowClose ∀ (modes: Modes) (open: Comments) (abilities: List Expr) (variable: Option (Comments, Word)):
    Parse.Gives GoodItems (() => rowClose modes open abilities variable) (row => True) :=
  byWalking [givesExpectFixed]

theorem givesRowVariable ∀ (modes: Modes) (open: Comments) (abilities: List Expr):
    Parse.Gives GoodItems (() => rowVariable modes open abilities) (row => True) :=
  Parse.givesThen (Parse.givesAfter0 (reads0At modes Pipe) (pipe => givesRowPart modes pipe)) (variable _ =>
    givesRowClose modes open abilities variable)

theorem givesRowStart ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (open: Comments)
    (nested: Nested self)
    (lower: Bool) (second: Option Tok):
    Parse.Gives GoodItems (() => rowStart self modes open lower second) (row => True) :=
  match lower && isSome Colon second with
    | True => Parse.readsFatal
    | False =>
      Parse.givesThen
        (Parse.givesAfter0 (reads0At modes RBrace) (closed =>
          Parse.givesAfter0 (reads0At modes Pipe) (pipe => givesRowAbilities self modes nested closed pipe)))
        (abilities _ => givesRowVariable modes open abilities)

theorem givesRowOf ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self):
    Parse.Gives GoodItems (() => rowOf self modes) (row => True) :=
  Parse.givesThen (givesExpectFixed modes LBrace "`{`") (open _ =>
    Parse.givesAfter0 (reads0At modes Lower) (lower =>
      Parse.givesAfter0 (reads0PeekAt modes 1) (second => givesRowStart self modes open nested lower second)))

theorem givesEffectResult ∀ (self: Goal → {Parse Item} Expr) (allowed: Modes)
    (nested: Nested self):
    Parse.Gives GoodItems (() => effectResult self allowed) Out :=
  byWalking [givesRowOf]

-- A list, read for nothing but that it is read.

theorem givesListItemsEndAny ∀ (self: Goal → {Parse Item} Expr) (inner: Modes) (open: Word) (pair: (List Expr, Bool)):
    Parse.Gives GoodItems (() => listItemsEnd self inner open pair) (found => True) :=
  byWalking [givesExpectAny]

theorem givesListItemAny ∀ (self: Goal → {Parse Item} Expr) (inner: Modes)
    (nested: Nested self):
    Parse.Gives GoodItems (() => listItem self inner) (found => True) :=
  Parse.givesWeaken (givesListItem self inner nested) (found parsed => byComputing)

theorem givesListItemsFromAny ∀ (self: Goal → {Parse Item} Expr) (inner: Modes) (open: Word) (first: Expr)
    (nested: Nested self):
    Parse.Gives GoodItems (() => listItemsFrom self inner open first) (found => True) :=
  Parse.givesThen Parse.givesMark (here _ =>
    Parse.givesThen
      (givesCommaListFrom inner
        (count => inner.at RBracket)
        (() => listItem self inner)
        (found => True)
        (count => givesAt inner RBracket)
        (givesListItemAny self inner nested)
        (here.left + 1)
        1
        first
        []
        byComputing
        ())
      (pair _ => givesListItemsEndAny self inner open pair))

theorem givesListItemsAny ∀ (self: Goal → {Parse Item} Expr) (inner: Modes) (open: Word)
    (nested: Nested self):
    Parse.Gives GoodItems (() => listItems self inner open) (found => True) :=
  byWalking [givesListItemAny, givesListItemsFromAny]

theorem givesListAfterAny ∀ (self: Goal → {Parse Item} Expr) (inner: Modes) (open: Word)
    (nested: Nested self) (seen: Option Tok):
    Parse.Gives GoodItems (() => listAfter self inner open seen) (found => True) :=
  byWalking [givesListItemsAny, givesBump]

theorem givesListExprAny ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self):
    Parse.Gives GoodItems (() => listExpr self modes) (found => True) :=
  Parse.givesThen givesBump (open _ =>
    Parse.givesAfter0 (reads0Peek modes.inBrackets) (seen => givesListAfterAny self modes.inBrackets open nested seen))

-- The rest of what an atom can be.

theorem givesFactsEnd ∀ (kind: FactsKind) (keyword: Word) (list: Expr):
    Parse.Gives GoodItems (() => factsEnd kind keyword list) Out :=
  byWalking []

theorem givesFacts ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (token: Tok) (kind: FactsKind)
    (nested: Nested self)
    (plain: token.wordWithin1 = False):
    Parse.Gives GoodItems (() => facts self modes token kind) Out :=
  Parse.givesThen givesBump (keyword _ =>
    Parse.givesAfter0 (reads0At modes LBracket) (bracket =>
      match bracket with
        | True => Parse.givesThen (givesListExprAny self modes nested) (list _ => givesFactsEnd kind keyword list)
        | False => Parse.givesDone (Tok.atomFalseOfWord1 token plain)))

theorem givesIncludeAtom ∀ (modes: Modes): Parse.Gives GoodItems (() => includeAtom modes) Out :=
  Parse.givesThen givesBump (keyword _ =>
    Parse.givesAfter0 (reads0At modes Str) (path =>
      match path with
        | True => Parse.givesThen givesBump (taken _ => Parse.givesDone byComputing)
        | False => givesFail modes _))

theorem givesCasesAtom ∀ (modes: Modes): Parse.Gives GoodItems (() => casesAtom modes) Out :=
  Parse.givesAfter0 (reads0BareCases modes) (bare =>
    match bare with
      | True => Parse.givesThen givesBump (keyword _ => Parse.givesDone byComputing)
      | False => givesFail modes _)

theorem givesUniverseAtom ∀ (modes: Modes): Parse.Gives GoodItems (() => universeAtom modes) Out :=
  Parse.givesThen givesBump (keyword _ =>
    Parse.givesAfter0 reads0Left (items =>
      match items with
        | [level, ..rest] =>
          match named: level.kind == Num && !modes.stops level with
            | True =>
              match big: (level.text.toNat |> .getOrElse 0) > 65535 with
                | True => Parse.readsFatal
                | False => Parse.givesThen givesBump (digits _ => Parse.givesDone byComputing)
            | False => Parse.givesDone byComputing
        | [] => Parse.givesDone byComputing))

theorem givesSectionStart ∀ (modes: Modes): Parse.Gives GoodItems (() => sectionStart modes) Out :=
  Parse.givesThen givesBump (dot _ =>
    Parse.givesAfter0 reads0Left (items =>
      match items with
        | [name, ..rest] =>
          match named: name.kind == Lower && name.glued && !isQualified name && !modes.stops name with
            | True => Parse.givesThen givesBump (field _ => Parse.givesDone byComputing)
            | False => Parse.readsFatal
        | [] => Parse.readsFatal))

theorem givesInterpolationOpen ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self):
    Parse.Gives GoodItems (() => interpolationOpen self modes) (Parse.Perhaps (found => True)) :=
  byWalking [givesExpectAny]

theorem givesInterpolationOn ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self) (seen: Option Tok):
    Parse.Gives GoodItems (() => interpolationOn self modes seen) (Parse.Perhaps (found => True)) :=
  byWalking [givesBump, givesInterpolationOpen, givesFail]

theorem givesInterpolationEnd ∀ (modes: Modes) (ended: Bool):
    Parse.Gives GoodItems (() => interpolationEnd modes ended) (word => True) :=
  byWalking [givesBump, givesFail]

theorem givesInterpolations ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self):
    Parse.Gives GoodItems (() => interpolations self modes) (pieces => True) :=
  Parse.givesThen
    (Parse.givesWeaken
      [weaker := gathered => True]
      (Parse.givesLoop (Parse.givesAfter0 (reads0Peek modes) (seen => givesInterpolationOn self modes nested seen)))
      (found ok => byComputing))
    (gathered _ =>
      Parse.givesAfter0 (reads0At modes StrEnd) (ended =>
        Parse.givesThen (givesInterpolationEnd modes ended) (last _ => Parse.givesDone byComputing)))

theorem givesInterpolated ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self):
    Parse.Gives GoodItems (() => interpolated self modes) Out :=
  byWalking [givesBump, givesInterpolations]

theorem givesAtomRest ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (kind: Tok)
    (nested: Nested self):
    Parse.Gives GoodItems (() => atomRest self modes kind) Out :=
  byWalking [givesInterpolated, givesIncludeAtom, givesFacts, givesCasesAtom, givesUniverseAtom, givesRecordExpr,
    givesSectionStart, givesAtomMissing]
