namespace Syntax.FollowsDeclArms
import Std (Bool, DecEq, Eq, List, Nat, Option, Pair, Parse, Result, Text, Unit, Void)
import Syntax (..)
import Fmt (..)
import Fmt.Walk (..)
import Fmt.BlankProofs (blankPure)
import Syntax.DeafProofs (..)
import Syntax.FollowsBase (..)
import Syntax.FollowsLadder (..)
import Syntax.FollowsForms (..)
import Syntax.FollowsFormsBinders (..)
import Syntax.FollowsFormsArms (..)
import Syntax.FollowsFormsPatterns (..)
import Syntax.FollowsFormsBlocks (..)
import Syntax.FollowsStatements (..)
import Syntax.FollowsDecl (..)
import Syntax.FollowsDeclHeaders (..)
import Syntax.FollowsDeclBinders (..)

-- Arms.

theorem itemToken ∀ (item other: Item) (same: SameCode item other): item.leaf.token = other.leaf.token :=
  Eq.cong (found => found.leaf.token) same

theorem anyAbsurdAlike ∀ (patterns twins: List Pattern)
    (alike: List.All2 PatternsAlike patterns twins):
    anyAbsurd patterns = anyAbsurd twins :=
  calc anyAbsurd patterns
    _ = anyAbsurd (walkPatterns blankPure patterns) := anyAbsurdDeaf patterns
    _ = anyAbsurd (walkPatterns blankPure twins) := rewrite walkPatternsAlike patterns twins alike
    _ = anyAbsurd twins := Eq.flipped (anyAbsurdDeaf twins)

theorem followsDefinitionArm ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (alts: AltPatternFollows) (modes: Modes):
    Parse.Follows SameCode ArmAlike (() => definitionArm self modes) (() => definitionArm selfTwin modes) :=
  Parse.followsThen followsBump (bar barTwin bars =>
    Parse.followsThen (followsArmPatterns alts modes) (patterns patternsTwin patternses =>
      Parse.followsThen (followsGuardOf knot modes) (guard guardTwin guards =>
        let absurds: anyAbsurd patterns = anyAbsurd patternsTwin := anyAbsurdAlike patterns patternsTwin patternses
        rewrite absurds then
          Parse.followsMap
            (body => { bar, patterns, guard, body })
            (body => { bar = barTwin, patterns = patternsTwin, guard = guardTwin, body })
            (followsArmBody knot modes (anyAbsurd patternsTwin) "`=>` and the arm's body")
            (body bodyTwin bodies =>
              alikeArm bar barTwin bars patterns patternsTwin patternses guard guardTwin guards body bodyTwin bodies))))

theorem followsDefinitionArmStep ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (alts: AltPatternFollows) (modes: Modes) (d column: Nat) (items others: List Item)
    (same: List.All2 SameCode items others):
    Parse.Follows SameCode (Option.Alike ArmAlike) (() => definitionArmStep self modes d column items) (() =>
      definitionArmStep selfTwin modes d column others) :=
  match items, others with
    | [], [] => Parse.followsDone Trivial
    | [next, ..rest], [nextTwin, ..restTwin] =>
      let tokens: next.leaf.token = nextTwin.leaf.token := itemToken next nextTwin same.left
      let starts: (!next.leaf.token.lineStart) = (!nextTwin.leaf.token.lineStart) :=
        Eq.cong (token => !token.lineStart) tokens
      let ends: (next.leaf.token.column <= d || next.kind == KwWhere)
        = (nextTwin.leaf.token.column <= d || nextTwin.kind == KwWhere) :=
        Eq.cong (token => token.column <= d || token.kind == KwWhere) tokens
      let lines: (next.kind == Pipe && next.leaf.token.column == column)
        = (nextTwin.kind == Pipe && nextTwin.leaf.token.column == column) :=
        Eq.cong (token => token.kind == Pipe && token.column == column) tokens
      let pipes: (next.kind == Pipe) = (nextTwin.kind == Pipe) := Eq.cong (token => token.kind == Pipe) tokens
      match first: !next.leaf.token.lineStart, firstTwin: !nextTwin.leaf.token.lineStart with
        | True, True => followsFail modes "the end of the arm" (() => modes.fail "the end of the arm")
        | False, False =>
          match second: next.leaf.token.column <= d || next.kind == KwWhere, secondTwin: nextTwin.leaf.token.column <= d
            || nextTwin.kind == KwWhere with
            | True, True => Parse.followsDone Trivial
            | False, False =>
              match third: next.kind == Pipe && next.leaf.token.column == column, thirdTwin: nextTwin.kind == Pipe
                && nextTwin.leaf.token.column == column with
                | True, True =>
                  followsThenEq
                    [j := here => (let arm := definitionArm self { modes | allow = Some here }; Some arm)]
                    [k := here => (let arm := definitionArm selfTwin { modes | allow = Some here }; Some arm)]
                    followsOffset
                    (here =>
                      Parse.followsMap
                        (arm => Some arm)
                        (arm => Some arm)
                        (followsDefinitionArm knot alts { modes | allow = Some here })
                        (arm armTwin arms => arms))
                | False, False =>
                  match fourth: next.kind == Pipe, fourthTwin: nextTwin.kind == Pipe with
                    | True, True => followsFatalAny _ _
                    | False, False =>
                      followsFatalAny
                        "expected `|` and another arm, or the end of the definition, but found ${next.spelled}"
                        (() =>
                          Syntax.fatal
                            "expected `|` and another arm, or the end of the definition, but found ${nextTwin.spelled}")

theorem followsDefinitionArmsFrom ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (alts: AltPatternFollows) (modes: Modes) (d: Nat):
    Parse.Follows SameCode (List.All2 ArmAlike) (() => definitionArmsFrom self modes d) (() =>
      definitionArmsFrom selfTwin modes d) :=
  Parse.followsLoop
    (followsOn
      (items => definitionArmStep self modes d (modes.limit.getOrElse 0) items)
      (items => definitionArmStep selfTwin modes d (modes.limit.getOrElse 0) items)
      (itemList others same =>
        followsDefinitionArmStep knot alts modes d (modes.limit.getOrElse 0) itemList others same))

theorem followsDefinitionArmsOn ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (alts: AltPatternFollows) (modes: Modes) (d: Nat) (items others: List Item)
    (same: List.All2 SameCode items others):
    Parse.Follows SameCode (List.All2 ArmAlike) (() => definitionArmsOn self modes d items) (() =>
      definitionArmsOn selfTwin modes d others) :=
  match items, others with
    | [first, ..rest], [firstTwin, ..restTwin] =>
      let tokens: first.leaf.token = firstTwin.leaf.token := itemToken first firstTwin same.left
      rewrite tokens then
        match !firstTwin.leaf.token.lineStart with
          | True => followsFatalAny _ _
          | False =>
            match firstTwin.leaf.token.column <= d with
              | True =>
                followsFatalAny _ (() => Syntax.fatal "arms are indented further than the definition they belong to")
              | False => followsDefinitionArmsFrom knot alts { modes | limit = Some firstTwin.leaf.token.column } d
    | [], [] => followsFail modes "`|`" (() => modes.fail "`|`")

theorem followsDefinitionArms ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (alts: AltPatternFollows) (modes: Modes) (d: Nat):
    Parse.Follows SameCode (List.All2 ArmAlike) (() => definitionArms self modes d) (() =>
      definitionArms selfTwin modes d) :=
  byWalking [followsDefinitionArmsOn knot]

theorem followsArmsBody ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (alts: AltPatternFollows) (modes: Modes) (d: Nat):
    Parse.Follows SameCode DefBodyAlike (() => armsBody self modes d) (() => armsBody selfTwin modes d) :=
  Parse.followsMap
    (arms => Arms arms)
    (arms => Arms arms)
    (followsDefinitionArms knot alts modes d)
    (arms armsTwin alike => alikeArms arms armsTwin alike)

theorem isEquationAlike ∀ (result twin: Expr) (alike: ExprsAlike result twin): isEquation result = isEquation twin :=
  calc isEquation result
    _ = isEquation (result.walk blankPure) := isEquationDeaf result
    _ = isEquation (twin.walk blankPure) := rewrite alike
    _ = isEquation twin := Eq.flipped (isEquationDeaf twin)

theorem followsDefinitionBodyOn ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (alts: AltPatternFollows) (modes: Modes) (result resultTwin: Expr)
    (results: ExprsAlike result resultTwin)
    (d: Nat) (seen: Option Tok):
    Parse.Follows SameCode DefBodyAlike (() => definitionBodyOn self modes result d seen) (() =>
      definitionBodyOn selfTwin modes resultTwin d seen) :=
  match seen with
    | Some kind =>
      match kind == ColonEq with
        | True => followsAssignedBody knot modes
        | False =>
          match kind == Pipe with
            | True => followsArmsBody knot alts modes d
            | False =>
              match kind == Equals with
                | True => followsFatalAny _ _
                | False => followsFail modes "`:=` and the body, or arms starting with `|` on their own lines" (() =>
                  modes.fail "`:=` and the body, or arms starting with `|` on their own lines")
    | None =>
      rewrite isEquationAlike result resultTwin results then
        match isEquation resultTwin with
          | True => followsFatalAny _ _
          | False => Parse.followsDone alikePrimitive

theorem followsDefinitionBody ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (alts: AltPatternFollows) (modes: Modes) (result resultTwin: Expr)
    (results: ExprsAlike result resultTwin)
    (isInstance: Bool) (d: Nat):
    Parse.Follows SameCode DefBodyAlike (() => definitionBody self modes result isInstance d) (() =>
      definitionBody selfTwin modes resultTwin isInstance d) :=
  followsThenEq (followsPeek modes) (seen =>
    Parse.followsThen
      (followsDefinitionBodyOn knot alts modes result resultTwin results d seen)
      (body bodyTwin bodies => followsDefinitionChecked isInstance body bodyTwin bodies))

theorem followsDefinitionParts ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (alts: AltPatternFollows) (modes: Modes) (exportKeyword exportTwin opaqueKeyword opaqueTwin: Option Comments)
    (exports: Option.Alike Anything exportKeyword exportTwin)
    (opaques: Option.Alike Anything opaqueKeyword opaqueTwin) (local: Option Nat):
    Parse.Follows SameCode
      (PairAlike HeaderAlike DefBodyAlike)
      (() => definitionParts self modes exportKeyword opaqueKeyword local)
      (() => definitionParts selfTwin modes exportTwin opaqueTwin local) :=
  match local with
    | Some column => followsThenEq (followsDefKindOf modes) (kind =>
      Parse.followsThen followsFixedFrom (keyword keywordTwin keywords =>
        Parse.followsThen (followsDefinitionName modes) (name nameTwin names =>
          Parse.followsThen (followsForallPart modes kind) (forallKeyword forallTwin foralls =>
            Parse.followsThen (followsHeaderParams knot modes.sealed) (params paramsTwin paramses =>
              Parse.followsThen followsFixedFrom (colon colonTwin colons =>
                Parse.followsThen
                  (followsResultType knot ({ modes | lines = [{ column = 0, many = False, kind = DefHeaderLine }] }))
                  (result resultTwin results =>
                    Parse.followsThen
                      (followsDecreasingPart knot modes
                        ({ modes | lines = [{ column = 0, many = False, kind = DefHeaderLine }] })
                        (kind == DefInstance))
                      (clause clauseTwin clauses =>
                        followsThenEq (followsAfterDecreasingOf modes clause clauseTwin clauses) (afterDecreasing =>
                          Parse.followsThen
                            (followsUnfoldingPart modes afterDecreasing (kind == DefInstance))
                            (opacity opacityTwin opacities =>
                              followsThenEq
                                (followsAfterUnfoldingOf afterDecreasing opacity opacityTwin opacities)
                                (afterUnfolding =>
                                  followsThenEq
                                    (followsClauseConflict afterUnfolding opacity opacityTwin opacities)
                                    (conflict =>
                                      match conflict with
                                        | True =>
                                          followsFatalAny _ (() => Syntax.fatal "`decreasing` goes before `unfolding`")
                                        | False =>
                                          (Parse.followsMap
                                            (body =>
                                              (
                                                {
                                                  exportKeyword,
                                                  opaqueKeyword,
                                                  kind,
                                                  keyword,
                                                  name,
                                                  forallKeyword,
                                                  params,
                                                  colon,
                                                  result,
                                                  decreasingClause = clause,
                                                  unfoldingClause = opacity
                                                },
                                                body
                                              ))
                                            (body =>
                                              (
                                                {
                                                  exportKeyword = exportTwin,
                                                  opaqueKeyword = opaqueTwin,
                                                  kind,
                                                  keyword = keywordTwin,
                                                  name = nameTwin,
                                                  forallKeyword = forallTwin,
                                                  params = paramsTwin,
                                                  colon = colonTwin,
                                                  result = resultTwin,
                                                  decreasingClause = clauseTwin,
                                                  unfoldingClause = opacityTwin
                                                },
                                                body
                                              ))
                                            (followsDefinitionBody knot alts afterUnfolding result resultTwin results
                                              (kind == DefInstance)
                                              (local.getOrElse 0))
                                            (body bodyTwin bodies =>
                                              (
                                                alikeHeader exportKeyword exportTwin opaqueKeyword opaqueTwin exports
                                                    opaques kind keyword keywordTwin name nameTwin names forallKeyword
                                                    forallTwin foralls params paramsTwin paramses colon colonTwin result
                                                    resultTwin results clause clauseTwin clauses opacity opacityTwin
                                                    opacities,
                                                bodies
                                              )))))))))))))))
    | None => followsThenEq (followsDefKindOf modes) (kind =>
      Parse.followsThen followsFixedFrom (keyword keywordTwin keywords =>
        Parse.followsThen (followsDefinitionName modes) (name nameTwin names =>
          Parse.followsThen (followsForallPart modes kind) (forallKeyword forallTwin foralls =>
            Parse.followsThen (followsHeaderParams knot modes.sealed) (params paramsTwin paramses =>
              Parse.followsThen followsFixedFrom (colon colonTwin colons =>
                Parse.followsThen (followsResultType knot modes) (result resultTwin results =>
                  Parse.followsThen
                    (followsDecreasingPart knot modes modes (kind == DefInstance))
                    (clause clauseTwin clauses =>
                      followsThenEq (followsAfterDecreasingOf modes clause clauseTwin clauses) (afterDecreasing =>
                        Parse.followsThen
                          (followsUnfoldingPart modes afterDecreasing (kind == DefInstance))
                          (opacity opacityTwin opacities =>
                            followsThenEq
                              (followsAfterUnfoldingOf afterDecreasing opacity opacityTwin opacities)
                              (afterUnfolding =>
                                followsThenEq
                                  (followsClauseConflict afterUnfolding opacity opacityTwin opacities)
                                  (conflict =>
                                    match conflict with
                                      | True =>
                                        followsFatalAny _ (() => Syntax.fatal "`decreasing` goes before `unfolding`")
                                      | False =>
                                        followsThenEq
                                          (followsBodyModesOf afterUnfolding (kind == DefInstance) local)
                                          (bodyModes =>
                                            Parse.followsMap
                                              (body =>
                                                (
                                                  {
                                                    exportKeyword,
                                                    opaqueKeyword,
                                                    kind,
                                                    keyword,
                                                    name,
                                                    forallKeyword,
                                                    params,
                                                    colon,
                                                    result,
                                                    decreasingClause = clause,
                                                    unfoldingClause = opacity
                                                  },
                                                  body
                                                ))
                                              (body =>
                                                (
                                                  {
                                                    exportKeyword = exportTwin,
                                                    opaqueKeyword = opaqueTwin,
                                                    kind,
                                                    keyword = keywordTwin,
                                                    name = nameTwin,
                                                    forallKeyword = forallTwin,
                                                    params = paramsTwin,
                                                    colon = colonTwin,
                                                    result = resultTwin,
                                                    decreasingClause = clauseTwin,
                                                    unfoldingClause = opacityTwin
                                                  },
                                                  body
                                                ))
                                              (followsDefinitionBody knot alts bodyModes result resultTwin results
                                                (kind == DefInstance)
                                                (local.getOrElse 0))
                                              (body bodyTwin bodies =>
                                                (
                                                  alikeHeader exportKeyword exportTwin opaqueKeyword opaqueTwin exports
                                                      opaques kind keyword keywordTwin name nameTwin names forallKeyword
                                                      forallTwin foralls params paramsTwin paramses colon colonTwin
                                                      result resultTwin results clause clauseTwin clauses opacity
                                                      opacityTwin opacities,
                                                  bodies
                                                )))))))))))))))

-- Declarations: relations and the trees built from alike parts.

def importItemKey (item: ImportItem): ImportItem := { name = item.name.blank, alias = blankCommentsWord item.alias }

def ImportItemAlike (item twin: ImportItem): Prop := importItemKey item = importItemKey twin

def ImportedAlike (imported twin: Imported): Prop := imported.blank = twin.blank

theorem importItemsCons ∀ (item: ImportItem) (rest: List ImportItem):
    blankImportItems [item, ..rest] = [importItemKey item, ..blankImportItems rest] :=
  match item with | { name, alias } => byComputing

theorem importItemsBlank ∀ (items twins: List ImportItem)
    (alike: List.All2 ImportItemAlike items twins):
    blankImportItems items = blankImportItems twins :=
  List.all2Join
    [f := list => blankImportItems list]
    [key := importItemKey]
    (k rest => [k, ..rest])
    importItemsCons
    (x y same => same)
    items
    twins
    alike

theorem alikeImportItem ∀ (name nameTwin: Word)
    (names: WordsAlike name nameTwin) (alias aliasTwin: Option (Comments, Word))
    (aliases: Option.Alike (PairAlike Anything WordsAlike) alias aliasTwin):
    ImportItemAlike { name, alias } { name = nameTwin, alias = aliasTwin } :=
  calc importItemKey { name, alias }
    _ = { name = name.blank, alias = blankCommentsWord alias } := byComputing
    _ = { name = nameTwin.blank, alias = blankCommentsWord aliasTwin } :=
      rewrite names, commentsWordBlank alias aliasTwin aliases
    _ = importItemKey { name = nameTwin, alias = aliasTwin } := byComputing

theorem alikeImportAll ∀ (dots dotsTwin: Comments): ImportedAlike (ImportAll dots) (ImportAll dotsTwin) := byComputing

theorem alikeImportItems ∀ (items twins: List ImportItem)
    (alike: List.All2 ImportItemAlike items twins):
    ImportedAlike (ImportItems items) (ImportItems twins) :=
  calc (ImportItems items).blank
    _ = ImportItems (blankImportItems items) := byComputing
    _ = ImportItems (blankImportItems twins) := rewrite importItemsBlank items twins alike
    _ = (ImportItems twins).blank := byComputing

theorem alikeNamespace ∀ (keyword keywordTwin: Comments) (name nameTwin: Word)
    (names: WordsAlike name nameTwin):
    DeclsAlike (Namespace keyword name) (Namespace keywordTwin nameTwin) :=
  calc (Namespace keyword name).walk blankPure
    _ = Namespace Comments.none name.blank := byComputing
    _ = Namespace Comments.none nameTwin.blank := rewrite names
    _ = (Namespace keywordTwin nameTwin).walk blankPure := byComputing

theorem alikeImport ∀ (keyword keywordTwin: Comments) (path pathTwin: Word)
    (paths: WordsAlike path pathTwin)
    (open openTwin: Comments) (imported importedTwin: Imported)
    (importeds: ImportedAlike imported importedTwin) (close closeTwin: Comments):
    DeclsAlike
      (Import keyword path open imported close)
      (Import keywordTwin pathTwin openTwin importedTwin closeTwin) :=
  calc (Import keyword path open imported close).walk blankPure
    _ = Import Comments.none path.blank Comments.none imported.blank Comments.none := byComputing
    _ = Import Comments.none pathTwin.blank Comments.none importedTwin.blank Comments.none := rewrite paths, importeds
    _ = (Import keywordTwin pathTwin openTwin importedTwin closeTwin).walk blankPure := byComputing

theorem alikeTest ∀ (keyword keywordTwin: Comments) (name nameTwin: Word)
    (names: WordsAlike name nameTwin)
    (colonEq colonEqTwin: Comments) (body bodyTwin: Expr)
    (bodies: ExprsAlike body bodyTwin):
    DeclsAlike (Test keyword name colonEq body) (Test keywordTwin nameTwin colonEqTwin bodyTwin) :=
  calc (Test keyword name colonEq body).walk blankPure
    _ = Test Comments.none name.blank Comments.none (body.walk blankPure) := byComputing
    _ = Test Comments.none nameTwin.blank Comments.none (bodyTwin.walk blankPure) := rewrite names, bodies
    _ = (Test keywordTwin nameTwin colonEqTwin bodyTwin).walk blankPure := byComputing

theorem alikeRuleSetDecl ∀ (keyword keywordTwin: Comments) (name nameTwin: Word)
    (names: WordsAlike name nameTwin)
    (colonEq colonEqTwin: Comments) (set setTwin: RuleSet)
    (sets: RuleSetAlike set setTwin):
    DeclsAlike (RuleSetDecl keyword name colonEq set) (RuleSetDecl keywordTwin nameTwin colonEqTwin setTwin) :=
  calc (RuleSetDecl keyword name colonEq set).walk blankPure
    _ = RuleSetDecl Comments.none name.blank Comments.none (walkRuleSet blankPure set) := byComputing
    _ = RuleSetDecl Comments.none nameTwin.blank Comments.none (walkRuleSet blankPure setTwin) := rewrite names, sets
    _ = (RuleSetDecl keywordTwin nameTwin colonEqTwin setTwin).walk blankPure := byComputing

-- Operations.

def operationKey (operation: Operation): Operation :=
  { name = operation.name.blank, colon = Comments.none, annotation = operation.annotation.walk blankPure }

def OperationAlike (operation twin: Operation): Prop := operationKey operation = operationKey twin

theorem operationsCons ∀ (operation: Operation) (rest: List Operation):
    blankOperations (walkOperations blankPure [operation, ..rest])
      = [operationKey operation, ..blankOperations (walkOperations blankPure rest)] :=
  match operation with | { name, colon, annotation } => byComputing

theorem operationsBlank ∀ (items twins: List Operation)
    (alike: List.All2 OperationAlike items twins):
    blankOperations (walkOperations blankPure items) = blankOperations (walkOperations blankPure twins) :=
  List.all2Join
    [f := list => blankOperations (walkOperations blankPure list)]
    [key := operationKey]
    (k rest => [k, ..rest])
    operationsCons
    (x y same => same)
    items
    twins
    alike

theorem alikeOperation ∀ (name nameTwin: Word)
    (names: WordsAlike name nameTwin)
    (colon colonTwin: Comments) (annotation annotationTwin: Expr)
    (annotations: ExprsAlike annotation annotationTwin):
    OperationAlike { name, colon, annotation } { name = nameTwin, colon = colonTwin, annotation = annotationTwin } :=
  calc operationKey { name, colon, annotation }
    _ = { name = name.blank, colon = Comments.none, annotation = annotation.walk blankPure } := byComputing
    _ = { name = nameTwin.blank, colon = Comments.none, annotation = annotationTwin.walk blankPure } :=
      rewrite names, annotations
    _ = operationKey { name = nameTwin, colon = colonTwin, annotation = annotationTwin } := byComputing

theorem alikeAbility ∀ (keyword keywordTwin: Comments) (name nameTwin: Word)
    (names: WordsAlike name nameTwin) (params paramsTwin: List Group)
    (paramses: List.All2 GroupsAlike params paramsTwin)
    (whereKeyword whereTwin: Comments) (operations twins: List Operation)
    (alike: List.All2 OperationAlike operations twins):
    DeclsAlike
      (Ability keyword name params whereKeyword operations)
      (Ability keywordTwin nameTwin paramsTwin whereTwin twins) :=
  calc (Ability keyword name params whereKeyword operations).walk blankPure
    _ = Ability Comments.none name.blank
        (blankGroups (walkGroups blankPure params))
        Comments.none
        (blankOperations (walkOperations blankPure operations)) := byComputing
    _ = Ability Comments.none nameTwin.blank
        (blankGroups (walkGroups blankPure paramsTwin))
        Comments.none
        (blankOperations (walkOperations blankPure twins)) :=
      rewrite names, groupsBlankAlike params paramsTwin paramses, operationsBlank operations twins alike
    _ = (Ability keywordTwin nameTwin paramsTwin whereTwin twins).walk blankPure := byComputing

-- Data declarations.

def stepKey: (Index, Word) → (Index, Word)
  | (IndexBinder binder, arrow) => (IndexBinder (binder.walk blankPure).blank, arrow.blank)
  | (IndexType annotation, arrow) => (IndexType (annotation.walk blankPure), arrow.blank)

def IndexStepAlike (step twin: (Index, Word)): Prop := stepKey step = stepKey twin

theorem blankIndexStepsCons ∀ (step: (Index, Word)) (rest: List (Index, Word)):
    blankIndexSteps (walkIndices blankPure [step, ..rest])
      = [stepKey step, ..blankIndexSteps (walkIndices blankPure rest)] :=
  match step with | (IndexBinder _, _) | (IndexType _, _) => byComputing

theorem indexStepsBlank ∀ (steps twins: List (Index, Word))
    (alike: List.All2 IndexStepAlike steps twins):
    blankIndexSteps (walkIndices blankPure steps) = blankIndexSteps (walkIndices blankPure twins) :=
  List.all2Join
    [f := list => blankIndexSteps (walkIndices blankPure list)]
    [key := stepKey]
    (k rest => [k, ..rest])
    blankIndexStepsCons
    (x y same => same)
    steps
    twins
    alike

theorem alikeStepBinder ∀ (binder twin: Group)
    (binders: GroupsAlike binder twin) (arrow arrowTwin: Word)
    (arrows: WordsAlike arrow arrowTwin):
    IndexStepAlike (IndexBinder binder, arrow) (IndexBinder twin, arrowTwin) :=
  calc stepKey (IndexBinder binder, arrow)
    _ = (IndexBinder (binder.walk blankPure).blank, arrow.blank) := byComputing
    _ = (IndexBinder (twin.walk blankPure).blank, arrowTwin.blank) := rewrite binders, arrows
    _ = stepKey (IndexBinder twin, arrowTwin) := byComputing

theorem alikeStepType ∀ (annotation twin: Expr)
    (annotations: ExprsAlike annotation twin) (arrow arrowTwin: Word)
    (arrows: WordsAlike arrow arrowTwin):
    IndexStepAlike (IndexType annotation, arrow) (IndexType twin, arrowTwin) :=
  calc stepKey (IndexType annotation, arrow)
    _ = (IndexType (annotation.walk blankPure), arrow.blank) := byComputing
    _ = (IndexType (twin.walk blankPure), arrowTwin.blank) := rewrite annotations, arrows
    _ = stepKey (IndexType twin, arrowTwin) := byComputing

def indicesKey (indices: Option Indices): Option Indices := match indices with
  | Some { colon, steps, last } =>
    Some { colon = Comments.none, steps = blankIndexSteps (walkIndices blankPure steps), last = last.walk blankPure }
  | None => None

def IndicesAlike (indices twin: Option Indices): Prop := indicesKey indices = indicesKey twin

theorem alikeIndices ∀ (colon colonTwin: Comments) (steps twins: List (Index, Word))
    (alike: List.All2 IndexStepAlike steps twins) (last lastTwin: Expr)
    (lasts: ExprsAlike last lastTwin):
    IndicesAlike (Some { colon, steps, last }) (Some { colon = colonTwin, steps = twins, last = lastTwin }) :=
  calc indicesKey (Some { colon, steps, last })
    _ = Some {
        colon = Comments.none,
        steps = blankIndexSteps (walkIndices blankPure steps),
        last = last.walk blankPure
      } := byComputing
    _ = Some {
        colon = Comments.none,
        steps = blankIndexSteps (walkIndices blankPure twins),
        last = lastTwin.walk blankPure
      } := rewrite indexStepsBlank steps twins alike, lasts
    _ = indicesKey (Some { colon = colonTwin, steps = twins, last = lastTwin }) := byComputing

-- Fields and constructors.

def fieldKey (field: Field): Field := {
  attributes = walkAttributes blankPure field.attributes,
  name = field.name.blank,
  colon = Comments.none,
  annotation = field.annotation.walk blankPure,
  default = blankAfter (walkAfter blankPure field.default)
}

def FieldAlike (field twin: Field): Prop := fieldKey field = fieldKey twin

def FieldsAlike (fields twin: Fields): Prop := fields.walk blankPure = twin.walk blankPure

theorem fieldsCons ∀ (field: Field) (rest: List Field):
    blankFieldList (walkFieldList blankPure [field, ..rest])
      = [fieldKey field, ..blankFieldList (walkFieldList blankPure rest)] :=
  match field with | { attributes, name, colon, annotation, default } => byComputing

theorem fieldListBlank ∀ (fields twins: List Field)
    (alike: List.All2 FieldAlike fields twins):
    blankFieldList (walkFieldList blankPure fields) = blankFieldList (walkFieldList blankPure twins) :=
  List.all2Join
    [f := list => blankFieldList (walkFieldList blankPure list)]
    [key := fieldKey]
    (k rest => [k, ..rest])
    fieldsCons
    (x y same => same)
    fields
    twins
    alike

theorem alikeField ∀ (attributes twinAttributes: List Attributes)
    (attributeses: List.All2 AttributeGroupAlike attributes twinAttributes) (name nameTwin: Word)
    (names: WordsAlike name nameTwin)
    (colon colonTwin: Comments) (annotation annotationTwin: Expr)
    (annotations: ExprsAlike annotation annotationTwin) (default defaultTwin: Option (Comments, Expr))
    (defaults: Option.Alike (PairAlike Anything ExprsAlike) default defaultTwin):
    FieldAlike { attributes, name, colon, annotation, default } {
      attributes = twinAttributes,
      name = nameTwin,
      colon = colonTwin,
      annotation = annotationTwin,
      default = defaultTwin
    } :=
  calc fieldKey { attributes, name, colon, annotation, default }
    _ = {
        attributes = walkAttributes blankPure attributes,
        name = name.blank,
        colon = Comments.none,
        annotation = annotation.walk blankPure,
        default = blankAfter (walkAfter blankPure default)
      } := byComputing
    _ = {
        attributes = walkAttributes blankPure twinAttributes,
        name = nameTwin.blank,
        colon = Comments.none,
        annotation = annotationTwin.walk blankPure,
        default = blankAfter (walkAfter blankPure defaultTwin)
      } :=
      rewrite walkAttributesAlike attributes twinAttributes attributeses,
          names,
          annotations,
          afterAlike default defaultTwin defaults
    _ = fieldKey {
        attributes = twinAttributes,
        name = nameTwin,
        colon = colonTwin,
        annotation = annotationTwin,
        default = defaultTwin
      } := byComputing

theorem alikeFields ∀ (open openTwin: Comments) (fields twins: List Field)
    (alike: List.All2 FieldAlike fields twins) (trailing trailingTwin: Bool)
    (trailings: trailing = trailingTwin) (close closeTwin: Comments):
    FieldsAlike { open, fields, trailingComma = trailing, close } {
      open = openTwin,
      fields = twins,
      trailingComma = trailingTwin,
      close = closeTwin
    } :=
  calc ({ open, fields, trailingComma = trailing, close }: Fields).walk blankPure
    _ = {
        open = Comments.none,
        fields = blankFieldList (walkFieldList blankPure fields),
        trailingComma = trailing,
        close = Comments.none
      } := byComputing
    _ = {
        open = Comments.none,
        fields = blankFieldList (walkFieldList blankPure twins),
        trailingComma = trailingTwin,
        close = Comments.none
      } := rewrite fieldListBlank fields twins alike, trailings
    _ = ({ open = openTwin, fields = twins, trailingComma = trailingTwin, close = closeTwin }: Fields).walk blankPure :=
      byComputing

def partKey: ConstructorPart → ConstructorPart
  | PartGroup group => PartGroup (group.walk blankPure).blank
  | PartFields fields => PartFields (fields.walk blankPure)

def PartAlike (part twin: ConstructorPart): Prop := partKey part = partKey twin

theorem partsCons ∀ (part: ConstructorPart) (rest: List ConstructorPart):
    blankParts (walkParts blankPure [part, ..rest]) = [partKey part, ..blankParts (walkParts blankPure rest)] :=
  match part with | PartGroup _ | PartFields _ => byComputing

theorem partsBlank ∀ (parts twins: List ConstructorPart)
    (alike: List.All2 PartAlike parts twins):
    blankParts (walkParts blankPure parts) = blankParts (walkParts blankPure twins) :=
  List.all2Join
    [f := list => blankParts (walkParts blankPure list)]
    [key := partKey]
    (k rest => [k, ..rest])
    partsCons
    (x y same => same)
    parts
    twins
    alike

theorem alikePartGroup ∀ (group twin: Group)
    (groups: GroupsAlike group twin):
    PartAlike (PartGroup group) (PartGroup twin) :=
  calc partKey (PartGroup group)
    _ = PartGroup (group.walk blankPure).blank := byComputing
    _ = PartGroup (twin.walk blankPure).blank := rewrite groups
    _ = partKey (PartGroup twin) := byComputing

theorem alikePartFields ∀ (fields twin: Fields)
    (fieldses: FieldsAlike fields twin):
    PartAlike (PartFields fields) (PartFields twin) :=
  calc partKey (PartFields fields)
    _ = PartFields (fields.walk blankPure) := byComputing
    _ = PartFields (twin.walk blankPure) := rewrite fieldses
    _ = partKey (PartFields twin) := byComputing

def constructorKey (constructor: Constructor): Constructor := {
  bar = Comments.none,
  attributes = walkAttributes blankPure constructor.attributes,
  name = constructor.name.blank,
  fields = blankParts (walkParts blankPure constructor.fields),
  result = blankAfter (walkAfter blankPure constructor.result)
}

def ConstructorAlike (constructor twin: Constructor): Prop := constructorKey constructor = constructorKey twin

theorem constructorsCons ∀ (constructor: Constructor) (rest: List Constructor):
    blankConstructors (walkConstructors blankPure [constructor, ..rest])
      = [constructorKey constructor, ..blankConstructors (walkConstructors blankPure rest)] :=
  match constructor with | { bar, attributes, name, fields, result } => byComputing

theorem constructorsBlank ∀ (items twins: List Constructor)
    (alike: List.All2 ConstructorAlike items twins):
    blankConstructors (walkConstructors blankPure items) = blankConstructors (walkConstructors blankPure twins) :=
  List.all2Join
    [f := list => blankConstructors (walkConstructors blankPure list)]
    [key := constructorKey]
    (k rest => [k, ..rest])
    constructorsCons
    (x y same => same)
    items
    twins
    alike

theorem alikeConstructor ∀ (bar barTwin: Comments) (attributes twinAttributes: List Attributes)
    (attributeses: List.All2 AttributeGroupAlike attributes twinAttributes) (name nameTwin: Word)
    (names: WordsAlike name nameTwin) (fields twins: List ConstructorPart)
    (alike: List.All2 PartAlike fields twins) (result resultTwin: Option (Comments, Expr))
    (results: Option.Alike (PairAlike Anything ExprsAlike) result resultTwin):
    ConstructorAlike { bar, attributes, name, fields, result } {
      bar = barTwin,
      attributes = twinAttributes,
      name = nameTwin,
      fields = twins,
      result = resultTwin
    } :=
  calc constructorKey { bar, attributes, name, fields, result }
    _ = {
        bar = Comments.none,
        attributes = walkAttributes blankPure attributes,
        name = name.blank,
        fields = blankParts (walkParts blankPure fields),
        result = blankAfter (walkAfter blankPure result)
      } := byComputing
    _ = {
        bar = Comments.none,
        attributes = walkAttributes blankPure twinAttributes,
        name = nameTwin.blank,
        fields = blankParts (walkParts blankPure twins),
        result = blankAfter (walkAfter blankPure resultTwin)
      } :=
      rewrite walkAttributesAlike attributes twinAttributes attributeses,
          names,
          partsBlank fields twins alike,
          afterAlike result resultTwin results
    _ = constructorKey {
        bar = barTwin,
        attributes = twinAttributes,
        name = nameTwin,
        fields = twins,
        result = resultTwin
      } := byComputing

def dataBodyKey: DataBody → DataBody
  | Abstract => Abstract
  | Synonym equals annotation => Synonym Comments.none (annotation.walk blankPure)
  | RecordBody equals fields => RecordBody Comments.none (fields.walk blankPure)
  | Sum equals constructors => Sum Comments.none (blankConstructors (walkConstructors blankPure constructors))

def DataBodyAlike (body twin: DataBody): Prop := dataBodyKey body = dataBodyKey twin

theorem dataWalk ∀ (attributes: List Attributes) (isInterface: Bool) (keyword: Comments) (name: Word)
    (params: List Group) (indices: Option Indices) (body: DataBody):
    (Data attributes isInterface keyword name params indices body).walk blankPure
      = Data
        (walkAttributes blankPure attributes)
        isInterface
        Comments.none
        name.blank
        (blankGroups (walkGroups blankPure params))
        (indicesKey indices)
        (dataBodyKey body) :=
  match indices, body with | None | Some _, Abstract | Synonym _ _ | RecordBody _ _ | Sum _ _ => byComputing

theorem alikeAbstract: DataBodyAlike Abstract Abstract := byComputing

theorem alikeSynonym ∀ (equals equalsTwin: Comments) (annotation twin: Expr)
    (annotations: ExprsAlike annotation twin):
    DataBodyAlike (Synonym equals annotation) (Synonym equalsTwin twin) :=
  calc dataBodyKey (Synonym equals annotation)
    _ = Synonym Comments.none (annotation.walk blankPure) := byComputing
    _ = Synonym Comments.none (twin.walk blankPure) := rewrite annotations
    _ = dataBodyKey (Synonym equalsTwin twin) := byComputing

theorem alikeRecordBody ∀ (equals equalsTwin: Comments) (fields twin: Fields)
    (fieldses: FieldsAlike fields twin):
    DataBodyAlike (RecordBody equals fields) (RecordBody equalsTwin twin) :=
  calc dataBodyKey (RecordBody equals fields)
    _ = RecordBody Comments.none (fields.walk blankPure) := byComputing
    _ = RecordBody Comments.none (twin.walk blankPure) := rewrite fieldses
    _ = dataBodyKey (RecordBody equalsTwin twin) := byComputing

theorem alikeSum ∀ (equals equalsTwin: Comments) (constructors twins: List Constructor)
    (alike: List.All2 ConstructorAlike constructors twins):
    DataBodyAlike (Sum equals constructors) (Sum equalsTwin twins) :=
  calc dataBodyKey (Sum equals constructors)
    _ = Sum Comments.none (blankConstructors (walkConstructors blankPure constructors)) := byComputing
    _ = Sum Comments.none (blankConstructors (walkConstructors blankPure twins)) :=
      rewrite constructorsBlank constructors twins alike
    _ = dataBodyKey (Sum equalsTwin twins) := byComputing

theorem alikeData ∀ (attributes twinAttributes: List Attributes)
    (attributeses: List.All2 AttributeGroupAlike attributes twinAttributes)
    (isInterface: Bool) (keyword keywordTwin: Comments) (name nameTwin: Word)
    (names: WordsAlike name nameTwin) (params paramsTwin: List Group)
    (paramses: List.All2 GroupsAlike params paramsTwin) (indices indicesTwin: Option Indices)
    (indiceses: IndicesAlike indices indicesTwin) (body bodyTwin: DataBody)
    (bodies: DataBodyAlike body bodyTwin):
    DeclsAlike
      (Data attributes isInterface keyword name params indices body)
      (Data twinAttributes isInterface keywordTwin nameTwin paramsTwin indicesTwin bodyTwin) :=
  calc (Data attributes isInterface keyword name params indices body).walk blankPure
    _ = Data
        (walkAttributes blankPure attributes)
        isInterface
        Comments.none
        name.blank
        (blankGroups (walkGroups blankPure params))
        (indicesKey indices)
        (dataBodyKey body) := dataWalk attributes isInterface keyword name params indices body
    _ = Data
        (walkAttributes blankPure twinAttributes)
        isInterface
        Comments.none
        nameTwin.blank
        (blankGroups (walkGroups blankPure paramsTwin))
        (indicesKey indicesTwin)
        (dataBodyKey bodyTwin) :=
      rewrite walkAttributesAlike attributes twinAttributes attributeses,
          names,
          groupsBlankAlike params paramsTwin paramses,
          indiceses,
          bodies
    _ = (Data twinAttributes isInterface keywordTwin nameTwin paramsTwin indicesTwin bodyTwin).walk blankPure :=
      Eq.flipped (dataWalk twinAttributes isInterface keywordTwin nameTwin paramsTwin indicesTwin bodyTwin)

-- Namespace lines and imports.

theorem followsNamespaceAfter ∀ (modes: Modes) (keyword keywordTwin: Comments) (seen: Option Tok):
    Parse.Follows SameCode DeclsAlike (() => namespaceAfter modes keyword seen) (() =>
      namespaceAfter modes keywordTwin seen) :=
  match seen with
    | Some Upper =>
      Parse.followsMap
        (name => Namespace keyword name)
        (name => Namespace keywordTwin name)
        followsBump
        (name nameTwin names => alikeNamespace keyword keywordTwin name nameTwin names)
    | Some Lower => followsFatalAny _ _
    | _ => followsFail modes "a namespace, such as `Day05`" (() => modes.fail "a namespace, such as `Day05`")

theorem followsNamespaceLine ∀ (modes: Modes):
    Parse.Follows SameCode DeclsAlike (() => namespaceLine modes) (() => namespaceLine modes) :=
  byWalking [followsFixedFrom, followsNamespaceAfter]

theorem importNameGuard ∀ (modes: Modes) (item other: Item)
    (same: SameCode item other):
    ((item.kind == Lower || item.kind == Upper) && !isQualified item && !modes.stops item)
      = ((other.kind == Lower || other.kind == Upper) && !isQualified other && !modes.stops other) :=
  let kinds: item.kind = other.kind := deafItem Item.kind itemKindDeaf item other same
  let quals: isQualified item = isQualified other := deafItem isQualified isQualifiedDeaf item other same
  let stops: modes.stops item = modes.stops other := stopsSame modes item other same
  rewrite stops, quals, kinds

theorem followsImportAliasWord ∀ (modes: Modes) (name nameTwin: Word)
    (names: WordsAlike name nameTwin)
    (asWord asWordTwin: Comments) (items others: List Item)
    (same: List.All2 SameCode items others):
    Parse.Follows SameCode
      (Option.Alike (PairAlike Anything WordsAlike))
      (() => importAliasWord modes name asWord items)
      (() => importAliasWord modes nameTwin asWordTwin others) :=
  match items, others with
    | [alias, ..rest], [aliasTwin, ..restTwin] =>
      let guards := importNameGuard modes alias aliasTwin same.left
      let texts: alias.text = aliasTwin.text := deafItem Item.text itemTextDeaf alias aliasTwin same.left
      let upper: startsUpper name.text = startsUpper nameTwin.text :=
        Eq.cong startsUpper (wordTextSame name nameTwin names)
      match first: (alias.kind == Lower || alias.kind == Upper)
        && !isQualified alias
        && !modes.stops alias, second: (aliasTwin.kind == Lower || aliasTwin.kind == Upper)
        && !isQualified aliasTwin
        && !modes.stops aliasTwin with
        | True, True =>
          rewrite texts, upper then
            match startsUpper nameTwin.text != startsUpper aliasTwin.text with
              | True => followsFatalAny _ (() =>
                (let case := if startsUpper nameTwin.text then "a capital letter" else "a lower-case letter";
                 Syntax.fatal "`${nameTwin.text}` starts with ${case}, so its new name must too"))
              | False =>
                Parse.followsMap
                  (word => Some (asWord, word))
                  (word => Some (asWordTwin, word))
                  followsBump
                  (theWord wordTwin words => (Trivial, words))
        | False, False => followsFail modes "the name to use instead, as in `x as y`" (() =>
          modes.fail "the name to use instead, as in `x as y`")
    | [], [] => followsFail modes "the name to use instead, as in `x as y`" (() =>
      modes.fail "the name to use instead, as in `x as y`")

theorem followsImportAliasOn ∀ (modes: Modes) (name nameTwin: Word)
    (names: WordsAlike name nameTwin) (asNext: Bool):
    Parse.Follows SameCode (Option.Alike (PairAlike Anything WordsAlike)) (() => importAliasOn modes name asNext) (() =>
      importAliasOn modes nameTwin asNext) :=
  byWalking [followsFixedFrom, followsImportAliasWord]

theorem followsImportAlias ∀ (modes: Modes) (name nameTwin: Word)
    (names: WordsAlike name nameTwin):
    Parse.Follows SameCode (Option.Alike (PairAlike Anything WordsAlike)) (() => importAlias modes name) (() =>
      importAlias modes nameTwin) :=
  byWalking [followsWordAhead, followsImportAliasOn]

def ImportItemsFollow (modes: Modes) (path pathTwin: Word) (fuel: Nat): Prop :=
  ∀ (found twins: List ImportItem) => List.All2 ImportItemAlike found twins
    → Parse.Follows SameCode (List.All2 ImportItemAlike) (() => importItems fuel modes path found) (() =>
      importItems fuel modes pathTwin twins)

theorem followsImportTail ∀ (more: Nat) (modes: Modes) (path pathTwin: Word)
    (again: ImportItemsFollow modes path pathTwin more) (done twins: List ImportItem)
    (dones: List.All2 ImportItemAlike done twins) (comma: Bool):
    Parse.Follows SameCode (List.All2 ImportItemAlike) (() => importTail more modes path done comma) (() =>
      importTail more modes pathTwin twins comma) :=
  byWalking [] then (List.all2Reverse done twins dones)

theorem followsImportNamed ∀ (more: Nat) (modes: Modes) (path pathTwin: Word)
    (again: ImportItemsFollow modes path pathTwin more) (found twins: List ImportItem)
    (founds: List.All2 ImportItemAlike found twins):
    Parse.Follows SameCode (List.All2 ImportItemAlike) (() => importNamed more modes path found) (() =>
      importNamed more modes pathTwin twins) :=
  Parse.followsThen followsBump (name nameTwin names =>
    Parse.followsThen (followsImportAlias modes name nameTwin names) (alias aliasTwin aliases =>
      followsThenEq (followsAt modes Comma) (comma =>
        followsImportTail more modes path pathTwin again
          [{ name, alias }, ..found]
          [{ name = nameTwin, alias = aliasTwin }, ..twins]
          (Both (alikeImportItem name nameTwin names alias aliasTwin aliases) founds)
          comma)))

theorem followsImportStop ∀ (modes: Modes) (path pathTwin: Word) (found twins: List ImportItem)
    (founds: List.All2 ImportItemAlike found twins) (dots: Bool):
    Parse.Follows SameCode (List.All2 ImportItemAlike) (() => importStop modes path found dots) (() =>
      importStop modes pathTwin twins dots) :=
  let empties: found.isEmpty = twins.isEmpty := List.all2IsEmpty found twins founds
  rewrite empties then
    match dots && !twins.isEmpty with
      | True => followsFatalAny _ (() => Syntax.fatal (mixedImport pathTwin))
      | False => followsFail modes "a name to import" (() => modes.fail "a name to import")

theorem followsImportStopAt ∀ (modes: Modes) (path pathTwin: Word) (found twins: List ImportItem)
    (founds: List.All2 ImportItemAlike found twins):
    Parse.Follows SameCode (List.All2 ImportItemAlike) (() => importStop modes path found (modes.at DotDot)) (() =>
      importStop modes pathTwin twins (modes.at DotDot)) :=
  byWalking [followsImportStop]

theorem followsImportItemsOnSucc ∀ (more: Nat) (modes: Modes) (path pathTwin: Word)
    (again: ImportItemsFollow modes path pathTwin more) (found twins: List ImportItem)
    (founds: List.All2 ImportItemAlike found twins) (items others: List Item)
    (same: List.All2 SameCode items others):
    Parse.Follows SameCode (List.All2 ImportItemAlike) (() => importItemsOn (Succ more) modes path found items) (() =>
      importItemsOn (Succ more) modes pathTwin twins others) :=
  match items, others with
    | [item, ..rest], [other, ..restTwin] =>
      let guards := importNameGuard modes item other same.left
      match first: (item.kind == Lower || item.kind == Upper)
        && !isQualified item
        && !modes.stops item, second: (other.kind == Lower || other.kind == Upper)
        && !isQualified other
        && !modes.stops other with
        | True, True => followsImportNamed more modes path pathTwin again found twins founds
        | False, False => followsImportStopAt modes path pathTwin found twins founds
    | [], [] => followsImportStopAt modes path pathTwin found twins founds

theorem followsImportItems ∀ (fuel: Nat) (modes: Modes) (path pathTwin: Word) (found twins: List ImportItem)
    (founds: List.All2 ImportItemAlike found twins):
    Parse.Follows SameCode (List.All2 ImportItemAlike) (() => importItems fuel modes path found) (() =>
      importItems fuel modes pathTwin twins) :=
  followsOn
    (items => importItemsOn fuel modes path found items)
    (items => importItemsOn fuel modes pathTwin twins items)
    (itemList others same =>
      match fuel with
        | Succ more =>
          followsImportItemsOnSucc more modes path pathTwin
            (again twinsAgain agains => followsImportItems more modes path pathTwin again twinsAgain agains)
            found
            twins
            founds
            itemList
            others
            same
        | Zero => followsImportStopAt modes path pathTwin found twins founds)

theorem followsImportNames ∀ (modes: Modes) (path pathTwin: Word):
    Parse.Follows SameCode ImportedAlike (() => importNames modes path) (() => importNames modes pathTwin) :=
  followsFuel
    (fuel => (let items := importItems fuel modes path []; ImportItems items))
    (fuel => (let items := importItems fuel modes pathTwin []; ImportItems items))
    (fuel =>
      Parse.followsMap
        (items => ImportItems items)
        (items => ImportItems items)
        (followsImportItems fuel modes path pathTwin [] [] Trivial)
        (itemList twins alike => alikeImportItems itemList twins alike))

theorem followsImportAllEnd ∀ (path pathTwin: Word) (dots dotsTwin: Comments) (closed: Bool):
    Parse.Follows SameCode ImportedAlike (() => importAllEnd path dots closed) (() =>
      importAllEnd pathTwin dotsTwin closed) :=
  byWalking [followsFatalAny]

theorem followsImportedOf ∀ (modes: Modes) (path pathTwin: Word) (dots: Bool):
    Parse.Follows SameCode ImportedAlike (() => importedOf modes path dots) (() => importedOf modes pathTwin dots) :=
  byWalking [followsFixedFrom, followsImportAllEnd, followsImportNames]

theorem followsImportClose ∀ (modes: Modes) (keyword keywordTwin: Comments) (path pathTwin: Word)
    (paths: WordsAlike path pathTwin)
    (open openTwin: Comments) (imported importedTwin: Imported)
    (importeds: ImportedAlike imported importedTwin):
    Parse.Follows SameCode DeclsAlike (() => importClose modes keyword path open imported) (() =>
      importClose modes keywordTwin pathTwin openTwin importedTwin) :=
  byWalking [followsExpectFixed] then (alikeImport keyword keywordTwin path pathTwin paths open openTwin imported
      importedTwin importeds close closeTwin)

theorem followsImportOpen ∀ (modes: Modes) (keyword keywordTwin: Comments) (path pathTwin: Word)
    (paths: WordsAlike path pathTwin):
    Parse.Follows SameCode DeclsAlike (() => importOpen modes keyword path) (() =>
      importOpen modes keywordTwin pathTwin) :=
  Parse.followsThen (followsExpectFixed modes LParen "`(` and the names to import") (open openTwin opens =>
    followsThenEq (followsAt modes DotDot) (dots =>
      Parse.followsThen (followsImportedOf modes path pathTwin dots) (imported importedTwin importeds =>
        followsImportClose modes keyword keywordTwin path pathTwin paths open openTwin imported importedTwin
            importeds)))

theorem followsImportAfter ∀ (modes: Modes) (keyword keywordTwin: Comments) (path pathTwin: Word)
    (paths: WordsAlike path pathTwin) (asNext: Bool):
    Parse.Follows SameCode DeclsAlike (() => importAfter modes keyword path asNext) (() =>
      importAfter modes keywordTwin pathTwin asNext) :=
  match asNext with
    | True => followsFatalAny _ (() =>
      Syntax.fatal "`import M as A` isn't Stitchwort: a namespace is imported as an item of the namespace above it")
    | False => followsImportOpen modes keyword keywordTwin path pathTwin paths

theorem followsImportPath ∀ (modes: Modes) (upper: Bool):
    Parse.Follows SameCode WordsAlike (() => importPath modes upper) (() => importPath modes upper) :=
  byWalking [followsFail]

theorem followsImportLine ∀ (modes: Modes):
    Parse.Follows SameCode DeclsAlike (() => importLine modes) (() => importLine modes) :=
  byWalking [followsFixedFrom, followsImportPath, followsWordAhead, followsImportAfter]
