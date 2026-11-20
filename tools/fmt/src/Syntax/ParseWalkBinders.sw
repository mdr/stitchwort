--| The binder parsers read for nothing but that they are read, and the lambdas, quantifiers and function types
--| read as parsers outside slice 1.

namespace Syntax.ParseWalkBinders
import Std (Bool, DecEq, Eq, List, Nat, Option, Pair, Parse, Result, Text)
import Syntax (..)
import Fmt (..)
import Syntax.LexProofs (..)
import Syntax.ParseProofs (..)
import Syntax.ParseWalk (..)
import Syntax.ParseWalkLadder (..)
import Syntax.ParseWalkOutside (..)
import Syntax.ParseWalkPatterns (..)
import Fmt.Grammar1 (..)
import Fmt.Kinds (..)

-- The binder parsers, read for nothing but that they are read.

theorem givesFullAny ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self):
    Parse.Gives GoodItems (() => full self modes) (expr => True) :=
  byWalking [givesSelfAny]

theorem givesRefuseAttributes ∀ (attributes: List Attributes) (what: Text):
    Parse.Gives GoodItems (() => refuseAttributes attributes what) (unit => True) :=
  byWalking []

theorem givesParamNameOn ∀ (modes: Modes) (seen: Option Tok):
    Parse.Gives GoodItems (() => paramNameOn modes seen) (word => True) :=
  match seen with
    | Some Upper | Some LParen | Some LBrace => givesFail modes _
    | other => givesLower modes "a parameter's name"

theorem givesParamName ∀ (modes: Modes): Parse.Gives GoodItems (() => paramName modes) (word => True) :=
  byWalking [givesParamNameOn]

theorem givesParamNames ∀ (modes: Modes): Parse.Gives GoodItems (() => paramNames modes) (found => True) :=
  Parse.givesWeaken
    (Parse.givesLoop
      [holds := word => True]
      (Parse.givesAfter0 (reads0At modes Lower) (atLower =>
        match atLower with
          | True => Parse.givesThen (givesParamName modes) (found _ => Parse.givesDone byComputing)
          | False => Parse.givesDone byComputing)))
    (found ok => byComputing)

theorem givesLowerNames ∀ (modes: Modes): Parse.Gives GoodItems (() => lowerNames modes) (found => True) :=
  Parse.givesWeaken
    (Parse.givesLoop
      [holds := word => True]
      (Parse.givesAfter0 (reads0At modes Lower) (atLower =>
        match atLower with
          | True => Parse.givesThen (givesLower modes "a name") (found _ => Parse.givesDone byComputing)
          | False => Parse.givesDone byComputing)))
    (found ok => byComputing)

theorem givesConsumedBare ∀ (started: Parse.Mark Item):
    Parse.Gives GoodItems (() => consumedBare started) (found => True) :=
  Parse.givesThen Parse.givesMark (here _ => Parse.givesDone byComputing)

theorem givesAllowBrace ∀ (modes: Modes): Parse.Gives GoodItems (() => allowBrace modes) (found => True) := byWalking []

theorem givesBinderTypeOn ∀ (self: Goal → {Parse Item} Expr) (allowed: Modes)
    (nested: Nested self)
    (seen: Option Tok) (items: List Item):
    Parse.Gives GoodItems (() => binderTypeOn self allowed seen items) (expr => True) :=
  match seen, items with
    | Some LBrace, [open, ..rest] =>
      match skipGroup [] [open, ..rest] with
        | Some [next, ..more] =>
          match typeStarts next.kind with
            | True => Parse.readsFatal
            | False => givesFullAny self allowed nested
        | other => givesFullAny self allowed nested
    | other, others => givesFullAny self allowed nested

theorem givesBinderTypeSeen ∀ (self: Goal → {Parse Item} Expr) (allowed: Modes)
    (nested: Nested self) (seen: Option Tok):
    Parse.Gives GoodItems (() => binderTypeSeen self allowed seen) (expr => True) :=
  byWalking [givesBinderTypeOn]

theorem givesBinderType ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self):
    Parse.Gives GoodItems (() => binderType self modes) (expr => True) :=
  byWalking [givesAllowBrace, givesBinderTypeSeen]

theorem givesHeaderDefault ∀ (self: Goal → {Parse Item} Expr) (inner: Modes)
    (nested: Nested self) (implicit atColonEq: Bool):
    Parse.Gives GoodItems (() => headerDefault self inner implicit atColonEq) (found => True) :=
  byWalking [givesFixedFrom, givesFullAny]

theorem givesHeaderGroupEnd ∀ (kind: GroupKind) (implicit: Bool) (open: Comments) (auto: Option Comments)
    (named: List Word) (colon: Comments) (annotation: Expr) (default: Option (Comments, Expr)) (close: Comments)
    (refused: Option Text) (consumed: Bool):
    Parse.Gives GoodItems
      (() => headerGroupEnd kind implicit open auto named colon annotation default close refused consumed)
      (found => True) :=
  byWalking []

theorem givesHeaderGroupColon ∀ (self: Goal → {Parse Item} Expr) (inner: Modes)
    (nested: Nested self)
    (kind: GroupKind) (refused: Option Text) (implicit: Bool) (started: Parse.Mark Item) (open: Comments)
    (auto: Option Comments) (named: List Word) (atColon: Bool):
    Parse.Gives GoodItems
      (() => headerGroupColon self inner kind refused implicit started open auto named atColon)
      (found => True) :=
  match atColon with
    | False => Parse.readsFatal
    | True => Parse.givesThen givesFixedFrom (colon _ =>
      Parse.givesThen (givesBinderType self inner nested) (annotation _ =>
        Parse.givesThen
          (Parse.givesAfter0 (reads0At inner ColonEq) (atColonEq =>
            givesHeaderDefault self inner nested implicit atColonEq))
          (default _ =>
            Parse.givesThen (givesExpectFixed inner (closerOf implicit) (closeMessage implicit auto named)) (close _ =>
              Parse.givesThen (givesConsumedBare started) (consumed _ =>
                givesHeaderGroupEnd kind implicit open auto named colon annotation default close refused consumed)))))

theorem givesHeaderGroupNamed ∀ (self: Goal → {Parse Item} Expr) (inner: Modes)
    (nested: Nested self)
    (kind: GroupKind) (refused: Option Text) (implicit: Bool) (started: Parse.Mark Item)
    (open: Comments) (split: (Option Comments, List Word)):
    Parse.Gives GoodItems (() => headerGroupNamed self inner kind refused implicit started open split) (found =>
      True) :=
  byWalking [givesHeaderGroupColon]

theorem givesHeaderGroupTyped ∀ (self: Goal → {Parse Item} Expr) (inner: Modes)
    (nested: Nested self)
    (kind: GroupKind) (refused: Option Text) (implicit: Bool) (started: Parse.Mark Item)
    (open: Comments) (names: List Word):
    Parse.Gives GoodItems (() => headerGroupTyped self inner kind refused implicit started open names) (found =>
      True) :=
  byWalking [givesHeaderGroupNamed]

theorem givesHeaderGroupAuto ∀ (self: Goal → {Parse Item} Expr) (inner: Modes)
    (nested: Nested self)
    (kind: GroupKind) (open: Comments) (auto: Word):
    Parse.Gives GoodItems (() => headerGroupAuto self inner kind open auto) (found => True) :=
  byWalking [givesFullAny, givesExpectFixed]

theorem givesHeaderGroupNames ∀ (self: Goal → {Parse Item} Expr) (inner: Modes)
    (nested: Nested self)
    (kind: GroupKind) (refused: Option Text) (implicit: Bool) (started: Parse.Mark Item) (open: Comments)
    (names: List Word) (typeFollows: Bool):
    Parse.Gives GoodItems
      (() => headerGroupNames self inner kind refused implicit started open names typeFollows)
      (found => True) :=
  byWalking [givesHeaderGroupAuto, givesHeaderGroupTyped]

theorem givesHeaderGroupParts ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (kind: GroupKind) (refused: Option Text) (implicit: Bool):
    Parse.Gives GoodItems (() => headerGroupParts self modes kind refused implicit) (found => True) :=
  Parse.givesThen Parse.givesMark (started _ =>
    Parse.givesThen givesFixedFrom (open _ =>
      Parse.givesThen (givesAttributesOf modes.inBrackets) (attributes _ =>
        Parse.givesThen (givesRefuseAttributes attributes "a definition's parameter") (refusal _ =>
          Parse.givesThen (givesParamName modes.inBrackets) (first _ =>
            Parse.givesThen (givesParamNames modes.inBrackets) (more _ =>
              Parse.givesThen (givesAt modes.inBrackets Colon) (atColon _ =>
                Parse.givesThen (givesAt modes.inBrackets RBracket) (atBracket _ =>
                  Parse.givesThen (givesOfReads0 (reads0Peek modes.inBrackets)) (peeked _ =>
                    givesHeaderGroupNames self modes.inBrackets nested kind refused implicit started open
                      [first, ..more]
                      (typeFollowsOf atColon atBracket peeked))))))))))

theorem givesHeaderGroupOn ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (kind: GroupKind) (refused: Option Text) (first second: Option Tok):
    Parse.Gives GoodItems (() => headerGroupOn self modes kind refused first second) (found => True) :=
  match first, second with
    | Some LParen, Some RParen =>
      Parse.givesThen givesFixedFrom (open _ => Parse.givesThen givesFixedFrom (close _ => Parse.givesDone byComputing))
    | Some LParen, other => givesHeaderGroupParts self modes nested kind refused False
    | Some LBracket, other => givesHeaderGroupParts self modes nested kind refused True
    | other, others => givesFail modes _

theorem givesHeaderGroup ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (kind: GroupKind) (refused: Option Text):
    Parse.Gives GoodItems (() => headerGroup self modes kind refused) (found => True) :=
  Parse.givesAfter0 (reads0Peek modes) (first =>
    Parse.givesAfter0 (reads0PeekAt modes 1) (second => givesHeaderGroupOn self modes nested kind refused first second))

theorem givesHeaderParams ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self):
    Parse.Gives GoodItems (() => headerParams self modes) (found => True) :=
  Parse.givesWeaken
    (Parse.givesLoop
      [holds := group => True]
      (Parse.givesAfter0 (reads0At modes Colon) (atColon =>
        match atColon with
          | True => Parse.givesDone byComputing
          | False => Parse.givesThen (givesHeaderGroup self modes nested GroupParam None) (group _ =>
            Parse.givesDone byComputing))))
    (found ok => byComputing)

theorem givesBinderDefault ∀ (self: Goal → {Parse Item} Expr) (inner: Modes)
    (nested: Nested self) (atColonEq: Bool):
    Parse.Gives GoodItems (() => binderDefault self inner atColonEq) (found => True) :=
  byWalking [givesFixedFrom, givesFullAny]

theorem givesBinderGroup ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self) (defaults: Bool):
    Parse.Gives GoodItems (() => binderGroup self modes defaults) (found => True) :=
  Parse.givesThen (givesExpectFixed modes LParen "`(`") (open _ =>
    Parse.givesThen (givesAttributesOf modes.inBrackets) (attributes _ =>
      Parse.givesThen (givesLower modes.inBrackets "a name") (first _ =>
        Parse.givesThen (givesLowerNames modes.inBrackets) (more _ =>
          Parse.givesThen (givesExpectFixed modes.inBrackets Colon "`:`") (colon _ =>
            Parse.givesThen (givesBinderType self modes.inBrackets nested) (annotation _ =>
              Parse.givesThen
                (Parse.givesAfter0 (reads0At modes.inBrackets ColonEq) (atColonEq =>
                  givesBinderDefault self modes.inBrackets nested atColonEq))
                (default _ =>
                  Parse.givesThen (givesExpectFixed modes.inBrackets RParen "`)`") (close _ =>
                    match !defaults && default.isSome with
                      | True => Parse.readsFatal
                      | False => Parse.givesDone byComputing))))))))

theorem givesImplicitNamed ∀ (self: Goal → {Parse Item} Expr) (inner: Modes)
    (nested: Nested self)
    (open: Comments) (attributes: List Attributes) (split: (Option Comments, List Word)):
    Parse.Gives GoodItems (() => implicitNamed self inner open attributes split) (found => True) :=
  byWalking [givesExpectFixed, givesBinderType]

theorem givesImplicitBinderOf ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self) (nameless: Bool):
    Parse.Gives GoodItems (() => implicitBinderOf self modes nameless) (found => True) :=
  byWalking [givesFixedFrom, givesFullAny, givesExpectFixed, givesAttributesOf, givesLower, givesLowerNames,
    givesImplicitNamed]

theorem givesImplicitBinder ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self):
    Parse.Gives GoodItems (() => implicitBinder self modes) (found => True) :=
  Parse.givesAfter0 [p := () => left()] reads0Left (items =>
    givesImplicitBinderOf self modes nested (namelessAutoAt items))

-- Lambdas, quantifiers and function types.

theorem givesPatternOf ∀ (modes: Modes): Parse.Gives GoodItems (() => patternOf modes) (pat => True) :=
  givesPattern { modes, level = PatternPlain }

theorem givesLambdaPattern ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self) (typed: Bool):
    Parse.Gives GoodItems (() => lambdaPattern self modes typed) (found => True) :=
  byWalking [givesBump, givesPatternOf, givesExpectAny, givesBinderType]

theorem givesLambdaGroup ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self):
    Parse.Gives GoodItems (() => lambdaGroup self modes) (found => True) :=
  byWalking [givesHeaderGroup]

theorem givesLambdaParen ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self) (items: List Item):
    Parse.Gives GoodItems (() => lambdaParen self modes items) (found => True) :=
  match annotatedParamAhead items with
    | True => givesLambdaGroup self modes nested
    | False => Parse.givesThen [p := () => Parse.mark()] Parse.givesMark (here _ =>
      givesLambdaPattern self modes nested (annotatedPatternAhead (here.left + 1) items))

theorem givesLambdaParam ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (items: List Item) (kind: Tok):
    Parse.Gives GoodItems (() => lambdaParam self modes items kind) (found => True) :=
  match kind with
    | Lower => Parse.givesThen (givesLower modes "a name") (name _ => Parse.givesDone byComputing)
    | Underscore => Parse.givesThen givesBump (name _ => Parse.givesDone byComputing)
    | LParen => givesLambdaParen self modes nested items
    | LBracket =>
      match implicitGroupAt items || namelessAutoAt items with
        | True => givesLambdaGroup self modes nested
        | False => Parse.givesDone byComputing
    | LBrace => Parse.givesThen (givesPatternOf modes) (found _ => Parse.givesDone byComputing)
    | other => Parse.givesDone byComputing

theorem givesLambdaStep ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self) (items: List Item):
    Parse.Gives GoodItems (() => lambdaStep self modes items) (found => True) :=
  byWalking [givesLambdaParam]

theorem givesLambdaParams ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self):
    Parse.Gives GoodItems (() => lambdaParams self modes) (found => True) :=
  Parse.givesWeaken
    (Parse.givesLoop
      [holds := param => True]
      (Parse.givesAfter0 reads0Left (items =>
        Parse.givesWeaken (givesLambdaStep self modes nested items) (found ok =>
          match found with
            | Some param => byComputing
            | None => byComputing))))
    (found ok => byComputing)

theorem givesLambda ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (keyword: Option Word)
    (nested: Nested self):
    Parse.Gives GoodItems (() => lambda self modes keyword) Out :=
  byWalking [givesLambdaParams, givesFail, givesExpectAny, givesFullAny]

theorem givesForallGroup ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self):
    Parse.Gives GoodItems (() => forallGroup self modes) (found => True) :=
  byWalking [givesHeaderGroup]

theorem givesForallParam ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (items: List Item) (item: Item):
    Parse.Gives GoodItems (() => forallParam self modes items item) (found => True) :=
  match item.kind with
    | Lower =>
      match isQualified item with
        | True => Parse.givesDone byComputing
        | False => Parse.givesThen givesBump (name _ => Parse.givesDone byComputing)
    | Underscore => Parse.givesThen givesBump (name _ => Parse.givesDone byComputing)
    | LParen =>
      match annotatedParamAhead items with
        | True => givesForallGroup self modes nested
        | False => Parse.givesDone byComputing
    | LBracket =>
      match implicitGroupAt items || namelessAutoAt items with
        | True => givesForallGroup self modes nested
        | False => Parse.givesDone byComputing
    | other => Parse.givesDone byComputing

theorem givesForallStep ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self) (items: List Item):
    Parse.Gives GoodItems (() => forallStep self modes items) (found => True) :=
  byWalking [givesForallParam]

theorem givesForallParams ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self):
    Parse.Gives GoodItems (() => forallParams self modes) (found => True) :=
  Parse.givesWeaken
    (Parse.givesLoop
      [holds := param => True]
      (Parse.givesAfter0 reads0Left (items =>
        Parse.givesWeaken (givesForallStep self modes nested items) (found ok =>
          match found with
            | Some param => byComputing
            | None => byComputing))))
    (found ok => byComputing)

theorem givesForallArrow ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (keyword: Word) (params: List Param) (atArrow: Bool):
    Parse.Gives GoodItems (() => forallArrow self modes keyword params atArrow) Out :=
  byWalking [givesBump, givesFullAny, givesFail]

theorem givesForallExpr ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self):
    Parse.Gives GoodItems (() => forallExpr self modes) Out :=
  byWalking [givesBump, givesForallParams, givesFail, givesForallArrow]

theorem givesExistsLambda ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (keyword: Word) (ahead: Bool):
    Parse.Gives GoodItems (() => existsLambda self modes keyword ahead) Out :=
  byWalking [givesLambda, givesFail]

theorem givesExistsExpr ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self):
    Parse.Gives GoodItems (() => existsExpr self modes) Out :=
  Parse.givesThen givesBump (keyword _ =>
    Parse.givesThen Parse.givesMark (here _ =>
      Parse.givesAfter0 [p := () => left()] reads0Left (items =>
        givesExistsLambda self modes nested keyword (lambdaAhead modes (here.left + 1) items))))

theorem givesQuantifierOn ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self) (items: List Item):
    Parse.Gives GoodItems (() => quantifierOn self modes items) Out :=
  match items with
    | [item, ..rest] =>
      match item.kind == KwForall with
        | True => givesForallExpr self modes nested
        | False => givesExistsExpr self modes nested
    | [] => givesExistsExpr self modes nested

theorem givesQuantifier ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self):
    Parse.Gives GoodItems (() => Syntax.quantifier self modes) Out :=
  byWalking [givesQuantifierOn]

theorem givesResultTypeAny ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self):
    Parse.Gives GoodItems (() => resultType self modes) (expr => True) :=
  Parse.givesAfter0 (reads0AllowBrace modes) (allowed =>
    Parse.givesAfter0 (reads0RowAhead allowed) (row =>
      match row with
        | True => Parse.givesWeaken (givesEffectResult self allowed nested) (found out => byComputing)
        | False => givesFullAny self allowed nested))

theorem givesPiBinder ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self) (implicit: Bool):
    Parse.Gives GoodItems (() => piBinder self modes implicit) (found => True) :=
  match implicit with
    | True => givesImplicitBinder self modes nested
    | False => givesBinderGroup self modes nested False

theorem givesPiExpr ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (implicit: Bool)
    (nested: Nested self):
    Parse.Gives GoodItems (() => piExpr self modes implicit) Out :=
  byWalking [givesPiBinder, givesRefuseAttributes, givesExpectAny, givesResultTypeAny]
