--| Local definitions, `let` and `cases`, the statements other than expressions, and the facts of the tiers above the
--| atoms; then each tier of `Outside` from `Nested` (`outsideOf`) and `givesExpressionAt`, which tie the walk's
--| assumptions to what is proved.

namespace Syntax.ParseWalkStatements
import Std (Bool, DecEq, Eq, List, Nat, Option, Pair, Parse, Result, Text)
import Syntax (..)
import Fmt (..)
import Syntax.LexProofs (..)
import Syntax.ParseProofs (..)
import Syntax.ParseWalk (..)
import Syntax.ParseWalkLadder (..)
import Syntax.ParseWalkOutside (..)
import Syntax.ParseWalkPatterns (..)
import Syntax.ParseWalkBinders (..)
import Syntax.ParseWalkMatch (..)
import Syntax.ParseWalkCalc (..)
import Syntax.ParseWalkFrame (..)
import Fmt.Grammar1 (..)
import Fmt.Kinds (..)

-- Local definitions, `let`, `cases`.

theorem givesLetPatternOf ∀ (modes: Modes) (isCtor: Bool):
    Parse.Gives GoodItems (() => letPatternOf modes isCtor) (pat => True) :=
  match isCtor with
    | True => Parse.givesThen givesBump (name _ =>
      givesCtorArgs pattern modes name (kind => kind == Equals || kind == ColonEq || kind == Colon) givesPattern)
    | False => givesPattern { modes, level = PatternTupleComponent }

theorem givesLetPattern ∀ (modes: Modes): Parse.Gives GoodItems (() => letPattern modes) (pat => True) :=
  Parse.givesAfter0 (reads0CtorAhead modes) (isCtor => givesLetPatternOf modes isCtor)

theorem givesLetAnnotation ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self) (atColon: Bool):
    Parse.Gives GoodItems (() => letAnnotation self modes atColon) (found => True) :=
  byWalking [givesFixedFrom, givesSelfAny]

theorem givesLetEquals ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (depth: Nat) (keyword: Comments) (pat: Pattern) (annotation: Option (Comments, Expr)) (atEquals: Bool):
    Parse.Gives GoodItems (() => letEquals self modes depth keyword pat annotation atEquals) (found => True) :=
  byWalking [givesExpectFixed, givesFullAny]

theorem givesLetStatement ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self):
    Parse.Gives GoodItems (() => letStatement self modes) (found => True) :=
  byWalking [givesFixedFrom, givesHere, givesLetAnnotation, givesLetEquals, givesLetPattern]

theorem givesLetEnd ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (binding: Let) (semicolon: Comments) (atEnd: Bool):
    Parse.Gives GoodItems (() => letEnd self modes binding semicolon atEnd) Out :=
  byWalking [givesFullAny]

theorem givesLetBodyOf ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (binding: Let) (atSemi: Bool):
    Parse.Gives GoodItems (() => letBodyOf self modes binding atSemi) Out :=
  match atSemi with
    | False => givesFail modes _
    | True => Parse.givesThen givesFixedFrom (semicolon _ =>
      Parse.givesThen (givesOfReads0 reads0Left) (taken _ =>
        givesLetEnd self modes nested binding semicolon (letAtEnd taken)))

theorem givesLetBody ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self) (binding: Let):
    Parse.Gives GoodItems (() => letBody self modes binding) Out :=
  byWalking [givesLetBodyOf]

theorem givesLetExpr ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self):
    Parse.Gives GoodItems (() => letExpr self modes) Out :=
  Parse.givesThen (givesLetStatement self modes.sealed nested) (binding _ => givesLetBody self modes nested binding)

theorem givesCasesThen ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (keyword: Word) (atThen: Bool):
    Parse.Gives GoodItems (() => casesThen self modes keyword atThen) Out :=
  byWalking [givesFixedFrom, givesSelfAny]

theorem givesCasesIn ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (keyword: Word) (atIn: Bool):
    Parse.Gives GoodItems (() => casesIn self modes keyword atIn) Out :=
  byWalking [givesCasesThen]

theorem givesCasesExpr ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self):
    Parse.Gives GoodItems (() => casesExpr self modes) Out :=
  byWalking [givesBump, givesCasesIn]

theorem givesMatchedPiped ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (indent: Nat) (matched: Expr)
    (matchedOut: Out matched) (piped: Bool)
    (pipeChains: ∀ (modes: Modes) (indent: Nat) (value: Expr) => Parse.Gives GoodItems
      (() => pipeChain self modes indent value)
      (result => result = value ∨ Out result)):
    Parse.Gives GoodItems (() => matchedPiped self modes indent matched piped) Out :=
  match piped with
    | True => Parse.givesWeaken (pipeChains modes indent matched) (result chained =>
      match chained with
        | Inl same => rewrite same then matchedOut
        | Inr out => out)
    | False => Parse.givesDone matchedOut

theorem givesMatchPiped ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (pipeChains: ∀ (modes: Modes) (indent: Nat) (value: Expr) => Parse.Gives GoodItems
      (() => pipeChain self modes indent value)
      (result => result = value ∨ Out result)):
    Parse.Gives GoodItems (() => matchPiped self modes) Out :=
  Parse.givesThen (givesOfReads0 reads0HeadIndent) (column _ =>
    Parse.givesThen givesBump (keyword _ =>
      Parse.givesThen (givesMatchExpr self modes keyword nested) (matched matchedOut =>
        Parse.givesAfter0 (reads0AtPipe modes) (piped =>
          givesMatchedPiped self modes column matched matchedOut piped pipeChains))))

theorem givesExprKeyword ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (kind: Tok)
    (nested: Nested self)
    (compared: OutsideCompared self)
    (bases: AtomBases self):
    Parse.Gives GoodItems (() => exprKeyword self modes kind) Out :=
  match kind == KwHandle with
    | True => givesHandleExpr self modes nested
    | False =>
      match kind == KwLet with
        | True => givesLetExpr self modes nested
        | False =>
          match kind == KwCalc with
            | True => givesCalcExpr self modes nested compared bases
            | False =>
              match kind == KwRewrite with
                | True => givesRewriteExpr self modes nested compared.below.below bases
                | False =>
                  match kind == KwCases with
                    | True => givesCasesExpr self modes nested
                    | False => givesMatchPiped self modes nested compared.below.pipeChains

-- Statements other than expressions.

--| The header keeps the `export` and `opaque` keywords it was given (so a declaration with either is outside slice 1).
theorem givesDefinitionPartsAny ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (exportKeyword opaqueKeyword: Option Comments) (local: Option Nat)
    (nested: Nested self):
    Parse.Gives GoodItems (() => definitionParts self modes exportKeyword opaqueKeyword local) (parts =>
      parts.fst.exportKeyword = exportKeyword ∧ parts.fst.opaqueKeyword = opaqueKeyword) :=
  Parse.givesThen (givesDefKindOf modes) (kind _ =>
    Parse.givesThen givesFixedFrom (keyword _ =>
      Parse.givesThen (givesDefinitionName modes) (name nameOk =>
        Parse.givesThen (givesForallPart modes _) (forallKeyword _ =>
          Parse.givesThen (givesHeaderParams self modes.sealed nested) (params _ =>
            Parse.givesThen givesFixedFrom (colon _ =>
              Parse.givesThen (givesResultTypeAny self _ nested) (result _ =>
                Parse.givesThen (givesDecreasingPart self modes _ _ nested) (decreasingClause _ =>
                  Parse.givesThen (givesAfterDecreasingOf modes decreasingClause) (afterDecreasing _ =>
                    Parse.givesThen (givesUnfoldingPart modes afterDecreasing _) (unfoldingClause _ =>
                      Parse.givesThen (givesAfterUnfoldingOf afterDecreasing unfoldingClause) (afterUnfolding _ =>
                        Parse.givesAfter0 (reads0ClauseConflict afterUnfolding unfoldingClause) (conflict =>
                          match conflict with
                            | True => Parse.readsFatal
                            | False => Parse.givesThen (givesBodyModes afterUnfolding _ local) (bodyModes _ =>
                              Parse.givesThen (givesDefinitionBody self bodyModes result _ _ nested) (body bodyOk =>
                                Parse.givesDone (Both byComputing byComputing)))))))))))))))

theorem givesLocalDef ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (attributes: List Attributes)
    (nested: Nested self):
    Parse.Gives GoodItems (() => localDef self modes attributes) StatementOk :=
  Parse.givesThen givesColumnHere (d _ =>
    Parse.givesThen (givesDefinitionPartsAny self modes None None (Some d) nested) (parts _ =>
      match parts with
        | (header, body) =>
          match header.unfoldingClause, body with
            | Some clause, other => Parse.readsFatal
            | None, Primitive => Parse.readsFatal
            | None, other => Parse.givesDone byComputing))

theorem givesLocalAttributed ∀ (self: Goal → {Parse Item} Expr) (allowed: Modes) (attributes: List Attributes)
    (nested: Nested self) (atDef atTheorem: Bool):
    Parse.Gives GoodItems (() => localAttributed self allowed attributes atDef atTheorem) StatementOk :=
  byWalking [givesLocalDef]

theorem givesAttributedLocal ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (attributes: List Attributes)
    (nested: Nested self) (items: List Item):
    Parse.Gives GoodItems (() => attributedLocal self modes attributes items) StatementOk :=
  byWalking [givesLocalAttributed]

theorem givesLetStatementEnd ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (binding: Let) (atSemi: Bool):
    Parse.Gives GoodItems (() => letStatementEnd self modes binding atSemi) StatementOk :=
  match atSemi with
    | True => Parse.givesThen (givesLetBody self modes nested binding) (body out =>
      Parse.givesDone (inSliceOut (expr => 1 <= expr.level) out))
    | False => Parse.givesDone byComputing

theorem givesStatementOther ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (kind: Tok)
    (nested: Nested self):
    Parse.Gives GoodItems (() => statementOther self modes kind) StatementOk :=
  byWalking [givesLetStatement, givesLetStatementEnd, givesLocalDef, givesAttributesOf, givesAttributedLocal]

-- The facts of the tiers above the atoms, from the walks of the tiers below.

theorem givesBraceArgument ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (outside: OutsideAtoms self):
    Parse.Gives GoodItems (() => braceArgument self modes) Out :=
  Parse.givesThen
    (Parse.readsWeaken [weaker := read ctor => True] (givesAtomBases self nested outside modes) (read ctor found =>
      byComputing))
    (ctor _ => Parse.givesThen (givesRecordExpr self modes nested) (record _ => Parse.givesDone byComputing))

theorem givesPipeFunction ∀ (self: Goal → {Parse Item} Expr) (modes: Modes)
    (nested: Nested self)
    (outside: OutsideBraced self)
    (bases: AtomBases self) (lambdas: Bool):
    Parse.Gives GoodItems (() => pipeFunction self modes lambdas) (function => True) :=
  match lambdas with
    | True => Parse.givesWeaken (givesLambda self modes None nested) (function _ => byComputing)
    | False => Parse.givesAfter0 reads0Offset (start =>
      Parse.givesAfter0 (reads0At modes Dot) (section =>
        Parse.givesThen
          (givesAppendOf self (if section then { modes | sectionHead = Some start } else modes) nested outside bases)
          (operand _ =>
            match section with
              | True => Parse.givesDone byComputing
              | False => Parse.givesDone byComputing)))

theorem givesPipesFrom ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (indent: Nat)
    (nested: Nested self)
    (outside: OutsideBraced self)
    (bases: AtomBases self)
    (fuel: Nat) (value: Expr):
    Parse.Gives GoodItems (() => pipesFrom fuel self modes indent value) (result => result = value ∨ Out result) :=
  match fuel with
    | Zero =>
      Parse.givesAfter0
        [p := () => left()]
        [j := items => pipesStep Zero self modes indent value (pipeAheadOn modes indent items)]
        reads0Left
        (items => Parse.givesDone (Inl byComputing))
    | Succ more => Parse.givesAfter0 [p := () => left()] reads0Left (items =>
      match pipeAheadOn modes indent items with
        | False => Parse.givesDone (Inl byComputing)
        | True => Parse.givesThen givesBump (operator _ =>
          Parse.givesAfter0 (reads0LambdaHere modes) (lambdas =>
            Parse.givesThen (givesPipeFunction self modes nested outside bases lambdas) (function _ =>
              Parse.givesWeaken
                (givesPipesFrom self modes indent nested outside bases more (Infix InfixPipe value operator function))
                (result same =>
                  match same with
                    | Inl equal => Inr (rewrite equal)
                    | Inr out => Inr out)))))

theorem givesPipeChain ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (indent: Nat) (value: Expr)
    (nested: Nested self)
    (outside: OutsideBraced self)
    (bases: AtomBases self):
    Parse.Gives GoodItems (() => pipeChain self modes indent value) (result => result = value ∨ Out result) :=
  Parse.givesThen Parse.givesMark (here _ =>
    givesPipesFrom self modes indent nested outside bases (here.left + 1) value)

theorem givesMembership ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (first: Option Tok) (element: Expr)
    (nested: Nested self)
    (outside: OutsidePiped self)
    (bases: AtomBases self):
    Parse.Gives GoodItems (() => membership self modes first element) Out :=
  byWalking [givesBump, givesPipedOf]

theorem givesChainLink ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (descending: Bool) (kind: Tok)
    (nested: Nested self)
    (outside: OutsidePiped self)
    (bases: AtomBases self):
    Parse.Gives GoodItems (() => chainLink self modes descending kind) (Parse.Perhaps (link => True)) :=
  byWalking [givesBump, givesPipedOf]

theorem givesChainOn ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (descending: Bool)
    (nested: Nested self)
    (outside: OutsidePiped self)
    (bases: AtomBases self):
    Parse.Gives GoodItems (() => chainOn self modes descending modes.peek) (Parse.Perhaps (link => True)) :=
  readsInPeeked modes
    (seen => chainOn self modes descending seen) _
    (start fine stops => Parse.givesDone byComputing start fine)
    (start item later shape fine stopped =>
      givesChainLink self modes descending item.kind nested outside bases start fine)

theorem givesChainLinks ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (descending: Bool)
    (nested: Nested self)
    (outside: OutsidePiped self)
    (bases: AtomBases self):
    Parse.Gives GoodItems (() => Syntax.chainLinks self modes descending) (List.All (link => True)) :=
  Parse.givesLoop (givesChainOn self modes descending nested outside bases)

theorem givesChainAfter ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (lhs: Expr) (operator: Word)
    (second: Expr) (descending: Bool)
    (nested: Nested self)
    (outside: OutsidePiped self)
    (bases: AtomBases self):
    Parse.Gives GoodItems (() => chainAfter self modes lhs operator second descending) Out :=
  byWalking [givesChainLinks]

theorem givesComparisonChain ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (lhs: Expr) (kind: Tok)
    (operator: Word) (second: Expr)
    (nested: Nested self)
    (outside: OutsidePiped self)
    (bases: AtomBases self):
    Parse.Gives GoodItems (() => comparisonChain self modes lhs kind operator second) Out :=
  byWalking [givesChainAfter]

theorem givesIffRight ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (quantified: Bool)
    (nested: Nested self)
    (outside: OutsideCompared self)
    (bases: AtomBases self):
    Parse.Gives GoodItems (() => iffRight self modes quantified) (right => True) :=
  match quantified with
    | True => Parse.givesWeaken (givesQuantifier self modes nested) (value _ => byComputing)
    | False => Parse.givesThen (givesCmpOf self modes nested outside bases) (compared parsed =>
      Parse.givesWeaken (givesLogicAfter self modes compared nested outside bases parsed) (value _ => byComputing))

theorem givesIff ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (logic: Expr)
    (nested: Nested self)
    (outside: OutsideCompared self)
    (bases: AtomBases self):
    Parse.Gives GoodItems (() => iff self modes logic) Out :=
  Parse.givesThen givesBump (operator _ =>
    Parse.givesAfter0 (reads0QuantifierAhead modes) (quantified =>
      Parse.givesThen (givesIffRight self modes quantified nested outside bases) (right _ =>
        Parse.givesAfter0 (reads0At modes IffArrow) (chained =>
          match chained with
            | True => Parse.readsFatal
            | False => Parse.givesDone byComputing))))

--| Each tier of `Outside` from `Nested` and what is not yet proved: a tier's facts are proved with the walks of the
--| tiers below it.
def outsideAtomsOf (self: Goal → {Parse Item} Expr) (nested: Nested self): OutsideAtoms self := {
  matches = (modes keyword => givesMatchExpr self modes keyword nested),
  clauseLambdas = (modes keyword => givesClauseLambda self modes keyword None ClauseMatches nested),
  records = (modes => givesRecordExpr self modes nested),
  annotations = (inner open first => givesAnnotated self inner open first nested),
  rightSections = (modes inside => givesRightSection self modes inside nested),
  parenOthers = (modes second third => givesParenOther self modes second third nested),
  namedArguments = (modes closer closeText => givesNamedArgument self modes closer closeText nested),
  rests = (modes kind => givesAtomRest self modes kind nested),
  missings = (modes => givesAtomMissing self modes)
}

def outsideBracedOf (self: Goal → {Parse Item} Expr) (nested: Nested self): OutsideBraced self := {
  below = outsideAtomsOf self nested,
  braceArguments = (modes => givesBraceArgument self modes nested (outsideAtomsOf self nested))
}

def outsidePipedOf (self: Goal → {Parse Item} Expr) (nested: Nested self): OutsidePiped self := {
  below = outsideBracedOf self nested,
  pipeChains = (modes indent value =>
    givesPipeChain self modes indent value nested
      (outsideBracedOf self nested)
      (givesAtomBases self nested (outsideAtomsOf self nested)))
}

def outsideComparedOf (self: Goal → {Parse Item} Expr) (nested: Nested self): OutsideCompared self := {
  below = outsidePipedOf self nested,
  comparisonChains = (modes lhs kind operator second =>
    givesComparisonChain self modes lhs kind operator second nested
      (outsidePipedOf self nested)
      (givesAtomBases self nested (outsideAtomsOf self nested))),
  cmpIfs = (modes lhs operator => givesCmpIf self modes lhs operator nested),
  memberships = (modes first element =>
    givesMembership self modes first element nested
      (outsidePipedOf self nested)
      (givesAtomBases self nested (outsideAtomsOf self nested))),
  quantifiers = (modes => givesQuantifier self modes nested)
}

def outsideIffedOf (self: Goal → {Parse Item} Expr) (nested: Nested self): OutsideIffed self := {
  below = outsideComparedOf self nested,
  iffs = (modes logic =>
    givesIff self modes logic nested
      (outsideComparedOf self nested)
      (givesAtomBases self nested (outsideAtomsOf self nested))),
  effectResults = (allowed => givesEffectResult self allowed nested),
  semis = (modes value => givesSemi self modes value nested)
}

--| Everything `Outside` says, from what is not yet proved and `Nested`.
def outsideOf (self: Goal → {Parse Item} Expr) (nested: Nested self): Outside self := {
  below = outsideIffedOf self nested,
  piExprs = (modes implicit => givesPiExpr self modes implicit nested),
  ifKeywords = (modes => givesIfKeyword self modes nested),
  lambdas = (modes => givesLambda self modes None nested),
  walks = (modes => givesWalkExpr self modes nested),
  keywords = (modes kind starts =>
    givesExprKeyword self modes kind nested
      (outsideComparedOf self nested)
      (givesAtomBases self nested (outsideAtomsOf self nested))),
  statementOthers = (modes kind starts => givesStatementOther self modes kind nested)
}

--| `expressionAt`, which starts the recursion from a declaration's level, reads what `GoalRead` says at every goal.
theorem givesExpressionAt: Nested expressionAt := goal =>
  Parse.readsRecursiveWith expressionRule
    (inner read expr => GoalRead inner read expr)
    (self nested argument => givesExpressionRule self argument nested (outsideOf self nested))
    goal
