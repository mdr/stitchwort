--| `meaning` is the file without comments, with `meaning`'s steps
--| (`meaningBlanksFirst`): so two files equal once their comments are
--| blanked have the same meaning, which stage 5's top theorem uses.
--|
--| Through the traversal lemma: blanking a node's own comments keeps what
--| `meaning`'s walk gives of it (`blankKeeps`), since that walk blanks the
--| same comments again. One lemma a blanking function, each "blank, walk,
--| blank is walk, blank".
namespace Fmt.BlankProofs
import Fmt (..)
import Fmt.Walk (..)
import Fmt.MeaningProofs (meaningAgrees, meaningPure)
import Std (Bool, Eq, Fail, List, Nat, Option, Result, Text)
import Syntax (..)

-- Small parts.

theorem wordsTwice ∀ (words: List Word): blankWords (blankWords words) = blankWords words := match words with
  | [] => byComputing
  | [word, ..rest] => rewrite wordsTwice rest

theorem commentsTwice ∀ (input: Option Comments): blankComments (blankComments input) = blankComments input := cases

theorem pairTwice ∀ (input: Option (Word, Word)): blankPair (blankPair input) = blankPair input := match input with
  | None | Some (_, _) => byComputing

theorem wordMapTwice ∀ (input: Option Word): (input.map Word.blank).map Word.blank = input.map Word.blank := cases

theorem commentsWordTwice ∀ (input: Option (Comments, Word)):
    blankCommentsWord (blankCommentsWord input) = blankCommentsWord input :=
  match input with | None | Some (_, _) => byComputing

theorem afterWalk ∀ (input: Option (Comments, Expr)):
    blankAfter (walkAfter meaningPure (blankAfter input)) = blankAfter (walkAfter meaningPure input) :=
  match input with | None | Some (_, _) => byComputing

theorem afterWordWalk ∀ (input: Option (Word, Expr)):
    blankAfterWord (walkAfter meaningPure (blankAfterWord input)) = blankAfterWord (walkAfter meaningPure input) :=
  match input with | None | Some (_, _) => byComputing

theorem baseWalk ∀ (input: Option (Expr, Word)):
    blankBase (walkBefore meaningPure (blankBase input)) = blankBase (walkBefore meaningPure input) :=
  match input with | None | Some (_, _) => byComputing

theorem tailWalk ∀ (input: Option (Word, Pattern)):
    blankAfterWord (walkTail meaningPure (blankAfterWord input)) = blankAfterWord (walkTail meaningPure input) :=
  match input with | None | Some (_, _) => byComputing

theorem linksWalk ∀ (links: List (Word, Expr)):
    blankLinks (walkLinks meaningPure (blankLinks links)) = blankLinks (walkLinks meaningPure links) :=
  match links with
    | [] => byComputing
    | [(word, value), ..rest] => rewrite linksWalk rest

theorem patternLinksWalk ∀ (links: List (Word, Pattern)):
    blankLinks (walkPatternLinks meaningPure (blankLinks links)) = blankLinks (walkPatternLinks meaningPure links) :=
  match links with
    | [] => byComputing
    | [(word, value), ..rest] => rewrite patternLinksWalk rest

-- Groups and parameters.

theorem groupWalk ∀ (group: Group): (group.blank.walk meaningPure).blank = (group.walk meaningPure).blank :=
  match group with
    | { kind, implicit, open, attributes, auto, names, colon, annotation, default, close, bare } =>
      rewrite wordsTwice names, commentsTwice auto, commentsTwice colon, afterWalk default

theorem groupPlainWalk ∀ (group: Group):
    (group.blank.walk meaningPure).blank.plainType = (group.walk meaningPure).blank.plainType :=
  rewrite groupWalk group

theorem groupsWalk ∀ (groups: List Group):
    blankGroups (walkGroups meaningPure (blankGroups groups)) = blankGroups (walkGroups meaningPure groups) :=
  match groups with
    | [] => byComputing
    | [group, ..rest] => rewrite groupWalk group, groupsWalk rest

theorem paramsWalk ∀ (params: List Param):
    blankParams (walkParams meaningPure (blankParams params)) = blankParams (walkParams meaningPure params) :=
  match params with
    | [] => byComputing
    | [NameParam _, ..rest] | [PatternParam _, ..rest] => rewrite paramsWalk rest
    | [Grouped group, ..rest] => rewrite groupWalk group, paramsWalk rest
    | [TypedPattern open pattern colon annotation close, ..rest] => rewrite paramsWalk rest

-- The records inside an expression.

theorem rowWalkBlank ∀ (row: Row): (walkRow meaningPure row.blank).blank = (walkRow meaningPure row).blank :=
  match row with | { open, abilities, variable, close } => rewrite commentsWordTwice variable

theorem piecesWalk ∀ (pieces: List Piece):
    blankPieces (walkPieces meaningPure (blankPieces pieces)) = blankPieces (walkPieces meaningPure pieces) :=
  match pieces with
    | [] => byComputing
    | [TextPiece _, ..rest] | [Interpolation _ _ _, ..rest] => rewrite piecesWalk rest

theorem scrutineesWalk ∀ (scrutinees: List Scrutinee):
    blankScrutinees (walkScrutinees meaningPure (blankScrutinees scrutinees))
      = blankScrutinees (walkScrutinees meaningPure scrutinees) :=
  match scrutinees with
    | [] => byComputing
    | [{ name, value }, ..rest] => rewrite pairTwice name, scrutineesWalk rest

theorem guardWalk ∀ (guard: Option Guard):
    (walkGuard meaningPure (guard.map Guard.blank)).map Guard.blank = (walkGuard meaningPure guard).map Guard.blank :=
  match guard with
    | None => byComputing
    | Some { keyword, binder, condition } => rewrite pairTwice binder

theorem armsWalk ∀ (arms: List Arm):
    blankArms (walkArms meaningPure (blankArms arms)) = blankArms (walkArms meaningPure arms) :=
  match arms with
    | [] => byComputing
    | [{ bar, patterns, guard, body }, ..rest] => rewrite guardWalk guard, afterWordWalk body, armsWalk rest

theorem letWalk ∀ (binding: Let): (walkLet meaningPure binding.blank).blank = (walkLet meaningPure binding).blank :=
  match binding with | { keyword, pattern, annotation, colonEq, value } => rewrite afterWalk annotation

theorem defBodyWalk ∀ (body: DefBody):
    (walkDefBody meaningPure body.blank).blank = (walkDefBody meaningPure body).blank :=
  match body with
    | Arms arms => rewrite armsWalk arms
    | _ => cases

theorem statementsWalk ∀ (statements: List Statement):
    blankStatements (walkStatements meaningPure (blankStatements statements))
      = blankStatements (walkStatements meaningPure statements) :=
  match statements with
    | [] => byComputing
    | [LetStatement binding, ..rest] => rewrite letWalk binding, statementsWalk rest
    | [LocalDef attributes header body, ..rest] => rewrite defBodyWalk body, statementsWalk rest
    | [ExprStatement value, ..rest] => rewrite statementsWalk rest

theorem statementWalk ∀ (statement: Statement):
    (walkStatement meaningPure statement.blank).blank = (walkStatement meaningPure statement).blank :=
  match statement with
    | LetStatement binding => rewrite letWalk binding
    | LocalDef attributes header body => rewrite defBodyWalk body
    | ExprStatement value => byComputing

theorem clausesWalk ∀ (clauses: List HandlerClause):
    blankClauses (walkClauses meaningPure (blankClauses clauses)) = blankClauses (walkClauses meaningPure clauses) :=
  match clauses with
    | [] => byComputing
    | [ReturnClause _ _ _ _ _, ..rest] | [OperationClause _ _ _ _ _ _ _, ..rest] => rewrite clausesWalk rest

theorem inductArmsWalk ∀ (arms: List InductArm):
    blankInductArms (walkInductArms meaningPure (blankInductArms arms))
      = blankInductArms (walkInductArms meaningPure arms) :=
  match arms with
    | [] => byComputing
    | [{ bar, case, names, arrow, body }, ..rest] => rewrite wordsTwice names, inductArmsWalk rest

theorem calcStepsWalk ∀ (steps: List CalcStep):
    blankCalcSteps (walkSteps meaningPure (blankCalcSteps steps)) = blankCalcSteps (walkSteps meaningPure steps) :=
  match steps with
    | [] => byComputing
    | [{ underscore, relation, operand, proof }, ..rest] => rewrite afterWalk proof, calcStepsWalk rest

theorem ruleListWalk ∀ (rules: List RewriteRule):
    blankRuleList (walkRuleList meaningPure (blankRuleList rules)) = blankRuleList (walkRuleList meaningPure rules) :=
  match rules with
    | [] => byComputing
    | [{ reverse, rule }, ..rest] =>
      match reverse with
        | None => rewrite ruleListWalk rest
        | Some _ => rewrite ruleListWalk rest

theorem rulesWalk ∀ (rules: Rules): (walkRules meaningPure rules.blank).blank = (walkRules meaningPure rules).blank :=
  match rules with
    | RuleList list => rewrite ruleListWalk list
    | Repeatedly word set => byComputing

-- The steps.

theorem blankExprWalk ∀ (expr: Expr): (blankExpr expr).walk meaningPure = expr.walk meaningPure := match expr with
  | Record open base fields comma close => rewrite baseWalk base
  | Chain first rest => rewrite linksWalk rest
  | Binding kind keyword params arrow body => rewrite wordMapTwice keyword, paramsWalk params
  | If keyword binder condition thenKeyword whenTrue elseKeyword whenFalse => rewrite pairTwice binder
  | Interpolated pieces => rewrite piecesWalk pieces
  | Match keyword scrutinees withKeyword arms => rewrite scrutineesWalk scrutinees, armsWalk arms
  | ClauseLambda keyword word arms => rewrite wordMapTwice word, armsWalk arms
  | FunctionType binder arrow result => rewrite groupPlainWalk binder
  | Effect row result => rewrite rowWalkBlank row
  | Block first rest result => rewrite statementWalk first, statementsWalk rest
  | LetIn binding semicolon body => rewrite letWalk binding
  | Handle _ _ _ clauses | Reify _ _ _ _ clauses => rewrite clausesWalk clauses
  | Induct keyword induct call withKeyword arms => rewrite inductArmsWalk arms
  | Calc keyword first steps => rewrite calcStepsWalk steps
  | Rewrite keyword rules target body => rewrite rulesWalk rules, afterWalk target, afterWalk body
  | Walk keyword items body => rewrite afterWalk body
  | _ => cases

theorem fieldPatternsWalk ∀ (fields: List FieldPattern):
    blankFieldPatterns (walkFieldPatterns meaningPure (blankFieldPatterns fields))
      = blankFieldPatterns (walkFieldPatterns meaningPure fields) :=
  match fields with
    | [] => byComputing
    | [{ name, value = (None | Some (_, _)) }, ..rest] => rewrite fieldPatternsWalk rest

theorem fieldsPatternWalk ∀ (fields: FieldsPattern):
    (walkFields meaningPure fields.blank).blank = (walkFields meaningPure fields).blank :=
  match fields with
    | { open, fields, trailingComma, rest, close } => rewrite fieldPatternsWalk fields, wordMapTwice rest

theorem fieldsPatternPlainWalk ∀ (fields: FieldsPattern):
    { (walkFields meaningPure fields.blank).blank | trailingComma = False }
      = { (walkFields meaningPure fields).blank | trailingComma = False } :=
  rewrite fieldsPatternWalk fields

theorem blankPatternWalk ∀ (pattern: Pattern): (blankPattern pattern).walk meaningPure = pattern.walk meaningPure :=
  match pattern with
    | PatternCtorFields _ fields | PatternRecord fields => rewrite fieldsPatternPlainWalk fields
    | PatternList open items comma tail close => rewrite tailWalk tail
    | PatternOr first rest => rewrite patternLinksWalk rest
    | _ => cases

theorem unfoldingTwice ∀ (input: Option (Comments, List Word)):
    blankUnfolding (blankUnfolding input) = blankUnfolding input :=
  match input with
    | None => byComputing
    | Some (word, names) => rewrite wordsTwice names

theorem blankHeaderWalk ∀ (header: Header):
    walkHeader meaningPure (blankHeader header) = walkHeader meaningPure header :=
  match header with
    | {
        exportKeyword,
        opaqueKeyword,
        kind,
        keyword,
        name,
        forallKeyword,
        params,
        colon,
        result,
        decreasingClause,
        unfoldingClause
      } =>
      rewrite commentsTwice exportKeyword,
          commentsTwice opaqueKeyword,
          groupsWalk params,
          afterWalk decreasingClause,
          unfoldingTwice unfoldingClause

-- Declarations.

theorem importItemsTwice ∀ (items: List ImportItem):
    blankImportItems (blankImportItems items) = blankImportItems items :=
  match items with
    | [] => byComputing
    | [{ name, alias }, ..rest] => rewrite commentsWordTwice alias, importItemsTwice rest

theorem importedTwice ∀ (imported: Imported): imported.blank.blank = imported.blank := match imported with
  | ImportItems items => rewrite importItemsTwice items
  | ImportAll _ => byComputing

theorem indexStepsWalk ∀ (steps: List (Index, Word)):
    blankIndexSteps (walkIndices meaningPure (blankIndexSteps steps))
      = blankIndexSteps (walkIndices meaningPure steps) :=
  match steps with
    | [] => byComputing
    | [(IndexBinder binder, arrow), ..rest] => rewrite groupWalk binder, indexStepsWalk rest
    | [(IndexType annotation, arrow), ..rest] => rewrite indexStepsWalk rest

theorem partsWalk ∀ (parts: List ConstructorPart):
    blankParts (walkParts meaningPure (blankParts parts)) = blankParts (walkParts meaningPure parts) :=
  match parts with
    | [] => byComputing
    | [PartGroup group, ..rest] => rewrite groupWalk group, partsWalk rest
    | [PartFields fields, ..rest] => rewrite partsWalk rest

theorem constructorsWalk ∀ (constructors: List Constructor):
    blankConstructors (walkConstructors meaningPure (blankConstructors constructors))
      = blankConstructors (walkConstructors meaningPure constructors) :=
  match constructors with
    | [] => byComputing
    | [{ bar, attributes, name, fields, result }, ..rest] =>
      rewrite partsWalk fields, afterWalk result, constructorsWalk rest

theorem operationsWalk ∀ (operations: List Operation):
    blankOperations (walkOperations meaningPure (blankOperations operations))
      = blankOperations (walkOperations meaningPure operations) :=
  match operations with
    | [] => byComputing
    | [{ name, colon, annotation }, ..rest] => rewrite operationsWalk rest

theorem blankDeclWalk ∀ (decl: Decl): (blankDecl decl).walk meaningPure = decl.walk meaningPure := match decl with
  | Import keyword path open imported close => rewrite importedTwice imported
  | Definition attributes header body => rewrite defBodyWalk body
  | Data attributes isInterface keyword name params indices body =>
    match indices, body with
      | None, Sum equals constructors => rewrite groupsWalk params, constructorsWalk constructors
      | Some { colon, steps, last }, Sum equals constructors =>
        rewrite groupsWalk params, indexStepsWalk steps, constructorsWalk constructors
      | None, _ => rewrite groupsWalk params then cases
      | Some { colon, steps, last }, _ => rewrite groupsWalk params, indexStepsWalk steps then cases
  | Ability keyword name params whereKeyword operations => rewrite groupsWalk params, operationsWalk operations
  | _ => cases

theorem fieldListWalk ∀ (fields: List Field):
    blankFieldList (walkFieldList meaningPure (blankFieldList fields))
      = blankFieldList (walkFieldList meaningPure fields) :=
  match fields with
    | [] => byComputing
    | [{ attributes, name, colon, annotation, default }, ..rest] => rewrite afterWalk default, fieldListWalk rest

theorem blankFieldsWalk ∀ (fields: Fields): (blankFields fields).walk meaningPure = fields.walk meaningPure :=
  match fields with | { open, fields, trailingComma, close } => rewrite fieldListWalk fields

theorem dottedTwice ∀ (parts: List (Comments, Word)):
    blankDottedParts (blankDottedParts parts) = blankDottedParts parts :=
  match parts with
    | [] => byComputing
    | [(word, part), ..rest] => rewrite dottedTwice rest

theorem attributeItemsTwice ∀ (items: List Attribute):
    blankAttributeItems (blankAttributeItems items) = blankAttributeItems items :=
  match items with
    | [] => byComputing
    | [{ name, parts, argument }, ..rest] => rewrite dottedTwice parts, wordMapTwice argument, attributeItemsTwice rest

theorem blankAttributesWalk ∀ (attributes: Attributes):
    { blankAttributes (blankAttributes attributes) | trailingComma = False }
      = { blankAttributes attributes | trailingComma = False } :=
  match attributes with | { at, open, items, trailingComma, close } => rewrite attributeItemsTwice items

theorem blankRuleSetWalk ∀ (set: RuleSet): walkRuleSet meaningPure (blankRuleSet set) = walkRuleSet meaningPure set :=
  match set with | { open, rules, trailingComma, close } => rewrite ruleListWalk rules

def blankPure: Pure := {
  expr = blankExpr,
  pattern = blankPattern,
  header = blankHeader,
  decl = blankDecl,
  fields = blankFields,
  attributes = blankAttributes,
  ruleSet = blankRuleSet
}

def blankAgrees: Agrees blankSteps blankPure := {
  expr = (z => byComputing),
  pattern = (z => byComputing),
  header = (z => byComputing),
  decl = (z => byComputing),
  fields = (z => byComputing),
  attributes = (z => byComputing),
  ruleSet = (z => byComputing)
}

def blankKeeps: Keeps blankPure meaningPure := {
  expr = blankExprWalk,
  pattern = blankPatternWalk,
  header = blankHeaderWalk,
  decl = blankDeclWalk,
  fields = blankFieldsWalk,
  attributes = blankAttributesWalk,
  ruleSet = blankRuleSetWalk
}

--| `meaning` is the file without comments, with `meaning`'s steps.
theorem meaningBlanksFirst ∀ (file: SourceFile): file.withoutComments.meaning = file.meaning :=
  rewrite applyKeeps file.withoutEnd blankSteps meaningSteps blankPure meaningPure blankAgrees meaningAgrees blankKeeps
