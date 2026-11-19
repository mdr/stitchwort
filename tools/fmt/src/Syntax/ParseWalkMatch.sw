--| `match`, clause lambdas and `handle`, handlers and `match induct` and `match reify`, and definitions' arms: the
--| parsers outside slice 1 that read arms, read for nothing but that they are read.

namespace Syntax.ParseWalkMatch
import Std (Bool, DecEq, Eq, List, Nat, Option, Pair, Parse, Result, Text)
import Syntax (..)
import Fmt (..)
import Syntax.Proofs (..)
import Syntax.ParseProofs (..)
import Syntax.ParseWalk (..)
import Syntax.ParseWalkOutside (..)
import Syntax.ParseWalkPatterns (..)
import Syntax.ParseWalkBinders (..)
import Fmt.Grammar1 (..)
import Fmt.Kinds (..)

-- `match`, clause lambdas, `handle`.

theorem givesScrutinee ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self):
    Parse.Gives GoodItems (() => scrutinee self modes) (found => True) :=
  Parse.givesThen (givesNamedBinder modes) (name _ =>
    Parse.givesThen (givesSelfAny self nested { modes = modes.sealed, level = LevelInline }) (value _ =>
      Parse.givesDone byComputing))

theorem givesArmColumn ∀ (column: Option Nat): Parse.Gives GoodItems (() => armColumn column) (found => True) :=
  givesAfter0 reads0Left (items => Parse.givesDone byComputing)

theorem givesGuardAt ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self) (atIf: Bool):
    Parse.Gives GoodItems (() => guardAt self modes atIf) (found => True) :=
  match atIf with
    | True => Parse.givesThen givesBump (keyword _ =>
      Parse.givesThen (givesNamedBinder modes) (binder _ =>
        Parse.givesThen (givesFullAny self { modes | guard = True, lines = [] } nested) (condition _ =>
          Parse.givesDone byComputing)))
    | False => Parse.givesDone byComputing

theorem givesGuardOf ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self):
    Parse.Gives GoodItems (() => guardOf self modes) (found => True) :=
  givesAfter0 (reads0At modes KwIf) (atIf => givesGuardAt self modes nested atIf)

theorem givesArmBodyOf ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (absurd: Bool) (what: Text) (atArrow: Bool):
    Parse.Gives GoodItems (() => armBodyOf self modes absurd what atArrow) (found => True) :=
  match absurd && !atArrow with
    | True => Parse.givesDone byComputing
    | False => Parse.givesThen (givesExpectAny modes FatArrow what) (arrow _ =>
      Parse.givesThen (givesFullAny self modes nested) (value _ => Parse.givesDone byComputing))

theorem givesArmBody ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (absurd: Bool) (what: Text):
    Parse.Gives GoodItems (() => armBody self modes absurd what) (found => True) :=
  givesAfter0 (reads0At modes FatArrow) (atArrow => givesArmBodyOf self modes nested absurd what atArrow)

theorem givesMatchArm ∀ (more: Nat) (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (scrutinees: Nat) (column: Option Nat) (found: List Arm):
    Parse.Gives GoodItems (() => matchArm more self modes scrutinees column found) (arms => True) :=
  Parse.givesThen givesBump (bar _ =>
    Parse.givesThen (givesArmPatterns modes) (patterns _ =>
      match patterns.length != scrutinees with
        | True => Parse.readsFatal _ _
        | False => Parse.givesThen (givesGuardOf self modes nested) (guard _ =>
          Parse.givesThen (givesArmBody self modes nested (anyAbsurd patterns) "`=>`") (body _ =>
            givesMatchArms more self modes nested scrutinees column [{ bar, patterns, guard, body }, ..found]))))

theorem givesMatchArmsAhead ∀ (fuel: Nat) (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (scrutinees: Nat) (column: Option Nat) (found: List Arm) (lined atPipe: Bool):
    Parse.Gives GoodItems (() => matchArmsAhead fuel self modes scrutinees column found lined atPipe) (arms => True) :=
  match fuel with
    | Succ more =>
      match atPipe && lined with
        | True => givesMatchArm more self modes nested scrutinees column found
        | False => Parse.givesDone byComputing
    | Zero => Parse.givesDone byComputing

theorem givesMatchArmsLined ∀ (fuel: Nat) (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (scrutinees: Nat) (found: List Arm) (columned: (Bool, Option Nat)):
    Parse.Gives GoodItems (() => matchArmsLined fuel self modes scrutinees found columned) (arms => True) :=
  match columned with
    | (lined, column) => givesAfter0 (reads0At modes Pipe) (atPipe =>
      givesMatchArmsAhead fuel self modes nested scrutinees column found lined atPipe)

theorem givesMatchArms ∀ (fuel: Nat) (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (scrutinees: Nat) (column: Option Nat) (found: List Arm):
    Parse.Gives GoodItems (() => matchArms fuel self modes scrutinees column found) (arms => True) :=
  Parse.givesThen (givesArmColumn column) (columned _ =>
    givesMatchArmsLined fuel self modes nested scrutinees found columned)

theorem givesClauseMatchesBody ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self) (atArrow: Bool):
    Parse.Gives GoodItems (() => clauseMatchesBody self modes atArrow) (found => True) :=
  match atArrow with
    | True => givesArmBody self modes nested False "`=>`"
    | False => Parse.givesDone byComputing

theorem givesClauseBody ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (kind: ClauseKind) (absurd: Bool):
    Parse.Gives GoodItems (() => clauseBody self modes kind absurd) (found => True) :=
  match kind with
    | ClauseMatches =>
      givesAfter0 (reads0At modes FatArrow) (atArrow => givesClauseMatchesBody self modes nested atArrow)
    | ClausePlain => givesArmBody self modes nested absurd "`=>`"
    | ClauseSome => givesArmBody self modes nested False "`=>`"

theorem givesClauseArmBody ∀ (more: Nat) (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (kind: ClauseKind) (column: Option Nat) (found: List Arm) (bar: Word) (patterns: List Pattern):
    Parse.Gives GoodItems (() => clauseArmBody more self modes kind column found bar patterns) (arms => True) :=
  Parse.givesThen (givesGuardOf self modes nested) (guard _ =>
    Parse.givesThen (givesClauseBody self modes nested kind (anyAbsurd patterns)) (body _ =>
      givesClauseArms more self modes nested kind (Some patterns.length) column [
        { bar, patterns, guard, body },
        ..found
      ]))

theorem givesClauseArm ∀ (more: Nat) (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (kind: ClauseKind) (count column: Option Nat) (found: List Arm):
    Parse.Gives GoodItems (() => clauseArm more self modes kind count column found) (arms => True) :=
  Parse.givesThen givesBump (bar _ =>
    Parse.givesThen (givesArmPatterns modes) (patterns _ =>
      match count with
        | Some first =>
          match first != patterns.length with
            | True => Parse.readsFatal _ _
            | False => givesClauseArmBody more self modes nested kind column found bar patterns
        | None => givesClauseArmBody more self modes nested kind column found bar patterns))

theorem givesClauseArmsAhead ∀ (fuel: Nat) (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (kind: ClauseKind) (count column: Option Nat) (found: List Arm) (lined atPipe: Bool):
    Parse.Gives GoodItems (() => clauseArmsAhead fuel self modes kind count column found lined atPipe) (arms => True) :=
  match fuel with
    | Succ more =>
      match atPipe && lined with
        | True => givesClauseArm more self modes nested kind count column found
        | False => Parse.givesDone byComputing
    | Zero => Parse.givesDone byComputing

theorem givesClauseArmsLined ∀ (fuel: Nat) (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (kind: ClauseKind) (count: Option Nat) (found: List Arm) (columned: (Bool, Option Nat)):
    Parse.Gives GoodItems (() => clauseArmsLined fuel self modes kind count found columned) (arms => True) :=
  match columned with
    | (lined, column) => givesAfter0 (reads0At modes Pipe) (atPipe =>
      givesClauseArmsAhead fuel self modes nested kind count column found lined atPipe)

theorem givesClauseArms ∀ (fuel: Nat) (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (kind: ClauseKind) (count column: Option Nat) (found: List Arm):
    Parse.Gives GoodItems (() => clauseArms fuel self modes kind count column found) (arms => True) :=
  Parse.givesThen (givesArmColumn column) (columned _ =>
    givesClauseArmsLined fuel self modes nested kind count found columned)

theorem givesClauseLambda ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (keyword: Word)
    (word: Option Word) (kind: ClauseKind)
    (nested: Nested self):
    Parse.Gives GoodItems (() => clauseLambda self modes keyword word kind) Out :=
  Parse.givesThen Parse.givesMark (here _ =>
    Parse.givesThen (givesClauseArms (here.left + 1) self modes nested kind None None []) (arms _ =>
      match arms.isEmpty with
        | True => givesFail modes _
        | False => Parse.givesDone byComputing))

-- Handlers and `match induct` and `match reify`.

theorem givesHandlerName ∀ (modes: Modes) (what: Text) (underscore: Bool):
    Parse.Gives GoodItems (() => handlerName modes what underscore) (word => True) :=
  match underscore with
    | True => givesBump
    | False => givesLower modes what

theorem givesHandlerNameAt ∀ (modes: Modes) (what: Text):
    Parse.Gives GoodItems (() => handlerName modes what (modes.at Underscore)) (word => True) :=
  givesAfter0 (reads0At modes Underscore) (underscore => givesHandlerName modes what underscore)

theorem givesOperationEnd ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (bar: Comments) (operation: Word) (argument: Pattern) (comma: Comments) (continuation: Word) (atComma: Bool):
    Parse.Gives GoodItems (() => operationEnd self modes bar operation argument comma continuation atComma) (found =>
      True) :=
  match atComma with
    | True => Parse.readsFatal _ _
    | False => Parse.givesThen (givesExpectFixed modes FatArrow "`=>`") (arrow _ =>
      Parse.givesThen (givesFullAny self modes nested) (body _ => Parse.givesDone byComputing))

theorem givesOperationClause ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (bar: Comments) (operation: Word) (argument: Pattern) (atArrow: Bool):
    Parse.Gives GoodItems (() => operationClause self modes bar operation argument atArrow) (found => True) :=
  match atArrow with
    | True => Parse.readsFatal _ _
    | False => Parse.givesThen (givesExpectFixed modes Comma "`,` and a name for the continuation") (comma _ =>
      Parse.givesThen (givesHandlerNameAt modes "a name for the continuation") (continuation _ =>
        givesAfter0 (reads0At modes Comma) (atComma =>
          givesOperationEnd self modes nested bar operation argument comma continuation atComma)))

theorem givesHandlerClauseOf ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (bar: Comments) (atReturn: Bool):
    Parse.Gives GoodItems (() => handlerClauseOf self modes bar atReturn) (found => True) :=
  match atReturn with
    | True => Parse.givesThen givesFixedFrom (keyword _ =>
      Parse.givesThen (givesHandlerNameAt modes "a name for the result") (name _ =>
        Parse.givesThen (givesExpectFixed modes FatArrow "`=>`") (arrow _ =>
          Parse.givesThen (givesFullAny self modes nested) (body _ => Parse.givesDone byComputing))))
    | False => Parse.givesThen (givesLowerQualifiedAny modes "an operation, or `return`") (op _ =>
      Parse.givesThen (givesPatternOf modes) (arg _ =>
        givesAfter0 (reads0At modes FatArrow) (atArrow => givesOperationClause self modes nested bar op arg atArrow)))

theorem givesHandlerClause ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self) (bar: Comments):
    Parse.Gives GoodItems (() => handlerClause self modes bar) (found => True) :=
  givesAfter0 (reads0At modes KwReturn) (atReturn => givesHandlerClauseOf self modes nested bar atReturn)

theorem givesClausesAhead ∀ (fuel: Nat) (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (column: Option Nat) (found: List HandlerClause) (lined atPipe: Bool):
    Parse.Gives GoodItems (() => clausesAhead fuel self modes column found lined atPipe) (clauses => True) :=
  match fuel with
    | Succ more =>
      match atPipe && lined with
        | True => Parse.givesThen givesFixedFrom (bar _ =>
          Parse.givesThen (givesHandlerClause self modes nested bar) (clause _ =>
            givesClausesFrom more self modes nested column [clause, ..found]))
        | False => Parse.givesDone byComputing
    | Zero => Parse.givesDone byComputing

theorem givesClausesLined ∀ (fuel: Nat) (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (found: List HandlerClause) (columned: (Bool, Option Nat)):
    Parse.Gives GoodItems (() => clausesLined fuel self modes found columned) (clauses => True) :=
  match columned with
    | (lined, column) =>
      givesAfter0 (reads0At modes Pipe) (atPipe => givesClausesAhead fuel self modes nested column found lined atPipe)

theorem givesClausesFrom ∀ (fuel: Nat) (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (column: Option Nat) (found: List HandlerClause):
    Parse.Gives GoodItems (() => clausesFrom fuel self modes column found) (clauses => True) :=
  Parse.givesThen (givesArmColumn column) (columned _ => givesClausesLined fuel self modes nested found columned)

theorem givesHandlerClauses ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self):
    Parse.Gives GoodItems (() => handlerClauses self modes) (clauses => True) :=
  Parse.givesThen Parse.givesMark (here _ =>
    Parse.givesThen (givesClausesFrom (here.left + 1) self modes nested None []) (clauses _ =>
      match clauses.isEmpty with
        | True => givesFail modes _
        | False => Parse.givesDone byComputing))

theorem givesHandleExpr ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self):
    Parse.Gives GoodItems (() => handleExpr self modes) Out :=
  Parse.givesThen givesFixedFrom (keyword _ =>
    Parse.givesThen (givesSelfAny self nested { modes = modes.sealed, level = LevelInline }) (computation _ =>
      Parse.givesThen (givesExpectFixed modes KwWith "`with`") (withKeyword _ =>
        Parse.givesThen (givesHandlerClauses self modes nested) (clauses _ => Parse.givesDone byComputing))))

theorem givesReifyComma ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (keyword reify: Comments) (computation: Expr) (comma: Bool):
    Parse.Gives GoodItems (() => reifyComma self modes keyword reify computation comma) Out :=
  match comma with
    | True => Parse.readsFatal _ _
    | False => Parse.givesThen (givesExpectFixed modes KwWith "`with`") (withKeyword _ =>
      Parse.givesThen (givesHandlerClauses self modes nested) (clauses _ => Parse.givesDone byComputing))

theorem givesReifyExpr ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (keyword reify: Comments)
    (nested: Nested self):
    Parse.Gives GoodItems (() => reifyExpr self modes keyword reify) Out :=
  Parse.givesThen (givesSelfAny self nested { modes = modes.sealed, level = LevelInline }) (computation _ =>
    givesAfter0 (reads0At modes Comma) (comma => givesReifyComma self modes nested keyword reify computation comma))

theorem givesCaseNamesOn ∀ (fuel: Nat) (modes: Modes) (found: List Word) (seen: Option Tok):
    Parse.Gives GoodItems (() => caseNamesOn fuel modes found seen) (names => True) :=
  match fuel, seen with
    | Succ more, Some Lower =>
      Parse.givesThen (givesLower modes "a name") (name _ => givesCaseNames more modes [name, ..found])
    | Succ more, Some Underscore => Parse.givesThen givesBump (name _ => givesCaseNames more modes [name, ..found])
    | Succ _ | Zero, _ => Parse.givesDone byComputing

theorem givesCaseNames ∀ (fuel: Nat) (modes: Modes) (found: List Word):
    Parse.Gives GoodItems (() => caseNames fuel modes found) (names => True) :=
  givesAfter0 (reads0Peek modes) (seen => givesCaseNamesOn fuel modes found seen)

theorem givesInductAhead ∀ (fuel: Nat) (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (column: Option Nat) (found: List InductArm) (lined atPipe: Bool):
    Parse.Gives GoodItems (() => inductAhead fuel self modes column found lined atPipe) (arms => True) :=
  match fuel with
    | Succ more =>
      match atPipe && lined with
        | True => Parse.givesThen givesFixedFrom (bar _ =>
          Parse.givesThen (givesLower modes "the name of a case of `f.induct`") (case _ =>
            Parse.givesThen Parse.givesMark (here _ =>
              Parse.givesThen (givesCaseNames (here.left + 1) modes []) (names _ =>
                Parse.givesThen (givesExpectFixed modes FatArrow "`=>`") (arrow _ =>
                  Parse.givesThen (givesFullAny self modes nested) (body _ =>
                    givesInductArms more self modes nested column [{ bar, case, names, arrow, body }, ..found]))))))
        | False => Parse.givesDone byComputing
    | Zero => Parse.givesDone byComputing

theorem givesInductLined ∀ (fuel: Nat) (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (found: List InductArm) (columned: (Bool, Option Nat)):
    Parse.Gives GoodItems (() => inductLined fuel self modes found columned) (arms => True) :=
  match columned with
    | (lined, column) =>
      givesAfter0 (reads0At modes Pipe) (atPipe => givesInductAhead fuel self modes nested column found lined atPipe)

theorem givesInductArms ∀ (fuel: Nat) (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (column: Option Nat) (found: List InductArm):
    Parse.Gives GoodItems (() => inductArms fuel self modes column found) (arms => True) :=
  Parse.givesThen (givesArmColumn column) (columned _ => givesInductLined fuel self modes nested found columned)

theorem givesInductComma ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (keyword induct: Comments) (call: Expr) (comma: Bool):
    Parse.Gives GoodItems (() => inductComma self modes keyword induct call comma) Out :=
  match comma with
    | True => Parse.readsFatal _ _
    | False => Parse.givesThen (givesExpectFixed modes KwWith "`with`") (withKeyword _ =>
      Parse.givesThen Parse.givesMark (here _ =>
        Parse.givesThen (givesInductArms (here.left + 1) self modes nested None []) (arms _ =>
          match arms.isEmpty with
            | True => givesFail modes _
            | False => Parse.givesDone byComputing)))

theorem givesInductExpr ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (keyword induct: Comments)
    (nested: Nested self):
    Parse.Gives GoodItems (() => inductExpr self modes keyword induct) Out :=
  Parse.givesThen (givesSelfAny self nested { modes = modes.sealed, level = LevelInline }) (call _ =>
    givesAfter0 (reads0At modes Comma) (comma => givesInductComma self modes nested keyword induct call comma))

theorem reads0SpecialAhead ∀ (modes: Modes) (word: Text): Reads0 (() => specialAhead modes word) :=
  reads0Then (reads0WordAhead modes word) (found => reads0Then (reads0PeekAt modes 1) (second => reads0Done _))

theorem givesMatchSome ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (keyword: Word)
    (some: Bool) (second: Option Tok)
    (nested: Nested self):
    Parse.Gives GoodItems (() => matchSome self modes keyword some second) Out :=
  match some && isSome Pipe second with
    | True => Parse.givesThen givesBump (name _ => givesClauseLambda self modes keyword (Some name) ClauseSome nested)
    | False => Parse.givesThen (givesScrutinee self modes nested) (first _ =>
      Parse.givesThen Parse.givesMark (here _ =>
        Parse.givesThen
          (givesCommaListFrom modes
            (count => False)
            (() => scrutinee self modes)
            (found => True)
            (count => Parse.givesDone byComputing)
            (givesScrutinee self modes nested)
            (here.left + 1)
            1
            first
            []
            byComputing
            ())
          (pair _ =>
            Parse.givesThen (givesExpectAny modes KwWith "`with`") (withKeyword _ =>
              Parse.givesThen Parse.givesMark (there _ =>
                Parse.givesThen (givesMatchArms (there.left + 1) self modes nested pair.fst.length None []) (arms _ =>
                  match arms.isEmpty with
                    | True => givesFail modes _
                    | False => Parse.givesDone byComputing))))))

theorem givesMatchPipe ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (keyword: Word)
    (nested: Nested self) (piped: Bool):
    Parse.Gives GoodItems (() => matchPipe self modes keyword piped) Out :=
  match piped with
    | True => givesClauseLambda self modes keyword None ClausePlain nested
    | False => givesAfter0 (reads0WordAhead modes "some") (some =>
      givesAfter0 (reads0PeekAt modes 1) (second => givesMatchSome self modes keyword some second nested))

theorem givesMatchReify ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (keyword: Word)
    (nested: Nested self) (reify: Bool):
    Parse.Gives GoodItems (() => matchReify self modes keyword reify) Out :=
  match reify with
    | True => Parse.givesThen givesFixedFrom (name _ => givesReifyExpr self modes keyword.comments name nested)
    | False => givesAfter0 (reads0At modes Pipe) (piped => givesMatchPipe self modes keyword nested piped)

theorem givesMatchSpecial ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (keyword: Word)
    (nested: Nested self) (induct: Bool):
    Parse.Gives GoodItems (() => matchSpecial self modes keyword induct) Out :=
  match induct with
    | True => Parse.givesThen givesFixedFrom (name _ => givesInductExpr self modes keyword.comments name nested)
    | False => givesAfter0 (reads0SpecialAhead modes "reify") (reify => givesMatchReify self modes keyword nested reify)

theorem givesMatchExpr ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (keyword: Word)
    (nested: Nested self):
    Parse.Gives GoodItems (() => matchExpr self modes keyword) Out :=
  givesAfter0 (reads0SpecialAhead modes "induct") (induct => givesMatchSpecial self modes keyword nested induct)

-- Definitions' arms.

theorem givesDefinitionArm ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self):
    Parse.Gives GoodItems (() => definitionArm self modes) (found => True) :=
  Parse.givesThen givesBump (bar _ =>
    Parse.givesThen (givesArmPatterns modes) (patterns _ =>
      Parse.givesThen (givesGuardOf self modes nested) (guard _ =>
        Parse.givesThen (givesArmBody self modes nested (anyAbsurd patterns) "`=>` and the arm's body") (body _ =>
          Parse.givesDone byComputing))))

theorem givesDefinitionArmStep ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (d column: Nat) (items: List Item):
    Parse.Gives GoodItems (() => definitionArmStep self modes d column items) (found => True) :=
  match items with
    | [] => Parse.givesDone byComputing
    | [next, ..rest] =>
      match !next.leaf.token.lineStart with
        | True => givesFail modes _
        | False =>
          match next.leaf.token.column <= d || next.kind == KwWhere with
            | True => Parse.givesDone byComputing
            | False =>
              match next.kind == Pipe && next.leaf.token.column == column with
                | True => Parse.givesThen (givesOfReads0 reads0Offset) (here _ =>
                  Parse.givesThen (givesDefinitionArm self { modes | allow = Some here } nested) (arm _ =>
                    Parse.givesDone byComputing))
                | False =>
                  match next.kind == Pipe with
                    | True => Parse.readsFatal _ _
                    | False => Parse.readsFatal _ _

theorem givesDefinitionArmsFrom ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self) (d: Nat):
    Parse.Gives GoodItems (() => definitionArmsFrom self modes d) (found => True) :=
  Parse.givesWeaken
    (Parse.givesLoop
      [holds := arm => True]
      (givesAfter0 reads0Left (items =>
        Parse.givesWeaken (givesDefinitionArmStep self modes nested d (modes.limit.getOrElse 0) items) (found ok =>
          match found with
            | Some arm => byComputing
            | None => byComputing))))
    (found ok => byComputing)

theorem givesDefinitionArmsOn ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (d: Nat) (items: List Item):
    Parse.Gives GoodItems (() => definitionArmsOn self modes d items) (found => True) :=
  match items with
    | [first, ..rest] =>
      match !first.leaf.token.lineStart with
        | True => Parse.readsFatal _ _
        | False =>
          match first.leaf.token.column <= d with
            | True => Parse.readsFatal _ _
            | False => givesDefinitionArmsFrom self { modes | limit = Some first.leaf.token.column } nested d
    | [] => givesFail modes _

theorem givesArmsBody ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (d: Nat)
    (nested: Nested self):
    Parse.Gives GoodItems (() => armsBody self modes d) BodyOk :=
  Parse.givesThen (givesAfter0 reads0Left (items => givesDefinitionArmsOn self modes nested d items)) (arms _ =>
    Parse.givesDone byComputing)
