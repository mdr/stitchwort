namespace Syntax.FollowsDeclBinders
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

-- Binders.

theorem walkAttributesEmpty ∀ (attributes: List Attributes):
    (walkAttributes blankPure attributes).isEmpty = attributes.isEmpty :=
  match attributes with | [] | [_, .._] => byComputing

theorem followsRefuseEmpty ∀ (attributes twins: List Attributes)
    (empties: attributes.isEmpty = twins.isEmpty) (what: Text):
    Parse.Follows SameCode Anything (() => refuseAttributes attributes what) (() => refuseAttributes twins what) :=
  match attributes, twins with
    | [], [] => Parse.followsDone Trivial
    | [x, ..xs], [y, ..ys] => followsFatalAny _ _

theorem groupWalkAttributes ∀ (group: Group):
    (group.walk blankPure).blank.attributes = walkAttributes blankPure group.attributes :=
  match group with
    | { kind, implicit, open, attributes, auto, names, colon, annotation, default, close, bare } => byComputing

theorem groupAttributesEmpty ∀ (group twin: Group)
    (alike: GroupsAlike group twin):
    group.attributes.isEmpty = twin.attributes.isEmpty :=
  let same: walkAttributes blankPure group.attributes = walkAttributes blankPure twin.attributes := calc walkAttributes
      blankPure group.attributes
    _ = (group.walk blankPure).blank.attributes := Eq.flipped (groupWalkAttributes group)
    _ = (twin.walk blankPure).blank.attributes := Eq.cong (found => found.attributes) alike
    _ = walkAttributes blankPure twin.attributes := groupWalkAttributes twin
  calc group.attributes.isEmpty
    _ = (walkAttributes blankPure group.attributes).isEmpty := Eq.flipped (walkAttributesEmpty group.attributes)
    _ = (walkAttributes blankPure twin.attributes).isEmpty := rewrite same
    _ = twin.attributes.isEmpty := walkAttributesEmpty twin.attributes

theorem optionIsSome ∀ [r: a → b → Prop] (found: Option a) (twin: Option b)
    (alike: Option.Alike r found twin):
    found.isSome = twin.isSome :=
  match found, twin with
    | Some x, Some y => byComputing
    | None, None => byComputing

theorem followsBinderDefault ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (inner: Modes) (atColonEq: Bool):
    Parse.Follows SameCode
      (Option.Alike (PairAlike Anything ExprsAlike))
      (() => binderDefault self inner atColonEq)
      (() => binderDefault selfTwin inner atColonEq) :=
  byWalking [followsFixedFrom]

theorem followsBinderGroup ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (modes: Modes) (defaults: Bool):
    Parse.Follows SameCode GroupsAlike (() => binderGroup self modes defaults) (() =>
      binderGroup selfTwin modes defaults) :=
  Parse.followsThen (followsExpectFixed modes LParen "`(`") (open openTwin opens =>
    Parse.followsThen (followsAttributesOf modes.inBrackets) (attributes attributesTwin attributeses =>
      Parse.followsThen (followsLower modes.inBrackets "a name") (first firstTwin firsts =>
        Parse.followsThen (followsLowerNames modes.inBrackets) (more moreTwin mores =>
          Parse.followsThen (followsExpectFixed modes.inBrackets Colon "`:`") (colon colonTwin colons =>
            Parse.followsThen (followsBinderType knot modes.inBrackets) (annotation annotationTwin annotations =>
              followsThenEq [alike := GroupsAlike] (followsAt modes.inBrackets ColonEq) (atEquals =>
                Parse.followsThen
                  (followsBinderDefault knot modes.inBrackets atEquals)
                  (default defaultTwin defaults2 =>
                    Parse.followsThen (followsExpectFixed modes.inBrackets RParen "`)`") (close closeTwin closes =>
                      let same: default.isSome = defaultTwin.isSome := optionIsSome default defaultTwin defaults2
                      rewrite same then
                        match !defaults && defaultTwin.isSome with
                          | True => followsFatalAny _ _
                          | False =>
                            Parse.followsDone
                              (alikeGroup GroupBinder False open openTwin attributes attributesTwin attributeses None
                                  None Trivial
                                  [first, ..more]
                                  [firstTwin, ..moreTwin]
                                  (Both firsts mores)
                                  (Some colon)
                                  (Some colonTwin)
                                  Trivial
                                  (Some annotation)
                                  (Some annotationTwin)
                                  annotations
                                  default
                                  defaultTwin
                                  defaults2
                                  close
                                  closeTwin
                                  False
                                  False))))))))))

theorem implicitAutoAlike ∀ (first firstTwin: Word)
    (firsts: WordsAlike first firstTwin) (rest restTwin: List Word)
    (rests: List.All2 WordsAlike rest restTwin):
    PairAlike
      (Option.Alike Anything)
      (List.All2 WordsAlike)
      (implicitAuto first rest)
      (implicitAuto firstTwin restTwin) :=
  match rest, restTwin with
    | [], [] => (Trivial, Both firsts Trivial)
    | [second, ..more], [secondTwin, ..moreTwin] =>
      let texts: first.text = firstTwin.text := wordTextSame first firstTwin firsts
      let guards: (first.text == "auto") = (firstTwin.text == "auto") := Eq.cong (text => text == "auto") texts
      match which: first.text == "auto", twin: firstTwin.text == "auto" with
        | True, True => (Trivial, rests)
        | False, False => (Trivial, Both firsts rests)

theorem followsImplicitNamed ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (inner: Modes) (open openTwin: Comments) (attributes attributesTwin: List Attributes)
    (attributeses: List.All2 AttributeGroupAlike attributes attributesTwin)
    (split splitTwin: (Option Comments, List Word))
    (splits: PairAlike (Option.Alike Anything) (List.All2 WordsAlike) split splitTwin):
    Parse.Follows SameCode GroupsAlike (() => implicitNamed self inner open attributes split) (() =>
      implicitNamed selfTwin inner openTwin attributesTwin splitTwin) :=
  match split, splitTwin with
    | (auto, names), (autoTwin, namesTwin) =>
      Parse.followsThen (followsExpectFixed inner Colon "`:`") (colon colonTwin colons =>
        Parse.followsThen (followsBinderType knot inner) (annotation annotationTwin annotations =>
          Parse.followsThen (followsExpectFixed inner RBracket "`]`") (close closeTwin closes =>
            Parse.followsDone
              (alikeGroup GroupBinder True open openTwin attributes attributesTwin attributeses auto autoTwin
                  splits.left names namesTwin splits.right
                  (Some colon)
                  (Some colonTwin)
                  Trivial
                  (Some annotation)
                  (Some annotationTwin)
                  annotations
                  None
                  None
                  Trivial
                  close
                  closeTwin
                  False
                  False))))

theorem followsImplicitBinderOf ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (modes: Modes) (nameless: Bool):
    Parse.Follows SameCode GroupsAlike (() => implicitBinderOf self modes nameless) (() =>
      implicitBinderOf selfTwin modes nameless) :=
  match nameless with
    | True => Parse.followsThen followsFixedFrom (open openTwin opens =>
      Parse.followsThen followsFixedFrom (auto autoTwin autos =>
        Parse.followsThen (followsFull knot modes.inBrackets) (annotation annotationTwin annotations =>
          Parse.followsThen (followsExpectFixed modes.inBrackets RBracket "`]`") (close closeTwin closes =>
            Parse.followsDone
              (alikeGroup GroupBinder True open openTwin [] [] Trivial
                (Some auto)
                (Some autoTwin)
                Trivial
                []
                []
                Trivial
                None
                None
                Trivial
                (Some annotation)
                (Some annotationTwin)
                annotations
                None
                None
                Trivial
                close
                closeTwin
                False
                False)))))
    | False => Parse.followsThen (followsExpectFixed modes LBracket "`[`") (open openTwin opens =>
      Parse.followsThen (followsAttributesOf modes.inBrackets) (attributes attributesTwin attributeses =>
        Parse.followsThen (followsLower modes.inBrackets "a name") (first firstTwin firsts =>
          Parse.followsThen (followsLowerNames modes.inBrackets) (rest restTwin rests =>
            followsImplicitNamed knot modes.inBrackets open openTwin attributes attributesTwin attributeses
              (implicitAuto first rest)
              (implicitAuto firstTwin restTwin)
              (implicitAutoAlike first firstTwin firsts rest restTwin rests)))))

theorem followsImplicitBinder ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin) (modes: Modes):
    Parse.Follows SameCode GroupsAlike (() => implicitBinder self modes) (() => implicitBinder selfTwin modes) :=
  followsOn
    (items => implicitBinderOf self modes (namelessAutoAt items))
    (items => implicitBinderOf selfTwin modes (namelessAutoAt items))
    (itemList others same =>
      rewrite deafOfStripped namelessAutoAt namelessAutoAtDeaf itemList others same then
        followsImplicitBinderOf knot modes (namelessAutoAt others))

theorem followsPiBinder ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (modes: Modes) (implicit: Bool):
    Parse.Follows SameCode GroupsAlike (() => piBinder self modes implicit) (() => piBinder selfTwin modes implicit) :=
  match implicit with
    | True => followsImplicitBinder knot modes
    | False => followsBinderGroup knot modes False

theorem followsPiExpr ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (modes: Modes) (implicit: Bool):
    Parse.Follows SameCode ExprsAlike (() => piExpr self modes implicit) (() => piExpr selfTwin modes implicit) :=
  Parse.followsThen (followsPiBinder knot modes implicit) (binder binderTwin binders =>
    Parse.followsThen
      (followsRefuseEmpty binder.attributes binderTwin.attributes
        (groupAttributesEmpty binder binderTwin binders)
        "a function type's parameter")
      (refusal refusalTwin refusals =>
        Parse.followsThen (followsExpect modes Arrow "`->`") (arrow arrowTwin arrows =>
          Parse.followsMap
            (result => FunctionType binder arrow result)
            (result => FunctionType binderTwin arrowTwin result)
            (followsResultType knot modes)
            (result resultTwin results =>
              alikeFunctionType binder binderTwin binders arrow arrowTwin arrows result resultTwin results))))

-- Definitions: headers and bodies.

def HeaderAlike (header twin: Header): Prop := walkHeader blankPure header = walkHeader blankPure twin

def DefBodyAlike (body twin: DefBody): Prop := (walkDefBody blankPure body).blank = (walkDefBody blankPure twin).blank

theorem groupsBlankAlike ∀ (groups twins: List Group)
    (alike: List.All2 GroupsAlike groups twins):
    blankGroups (walkGroups blankPure groups) = blankGroups (walkGroups blankPure twins) :=
  match groups, twins with
    | [], [] => byComputing
    | [x, ..xs], [y, ..ys] =>
      let (head, tail) := alike
      calc blankGroups (walkGroups blankPure [x, ..xs])
        _ = [(x.walk blankPure).blank, ..blankGroups (walkGroups blankPure xs)] := byComputing
        _ = [(y.walk blankPure).blank, ..blankGroups (walkGroups blankPure ys)] :=
          rewrite head, groupsBlankAlike xs ys tail
        _ = blankGroups (walkGroups blankPure [y, ..ys]) := byComputing

theorem unfoldingBlankAlike ∀ (found twin: Option (Comments, List Word))
    (alike: Option.Alike (PairAlike Anything (List.All2 WordsAlike)) found twin):
    blankUnfolding found = blankUnfolding twin :=
  match found, twin with
    | Some (c, names), Some (d, namesTwin) =>
      let same: blankWords names = blankWords namesTwin := namesBlank names namesTwin alike.right
      calc blankUnfolding (Some (c, names))
        _ = Some (Comments.none, blankWords names) := byComputing
        _ = Some (Comments.none, blankWords namesTwin) := rewrite same
        _ = blankUnfolding (Some (d, namesTwin)) := byComputing
    | None, None => byComputing

theorem alikeHeader ∀ (exportKeyword exportTwin opaqueKeyword opaqueTwin: Option Comments)
    (exports: Option.Alike Anything exportKeyword exportTwin)
    (opaques: Option.Alike Anything opaqueKeyword opaqueTwin)
    (kind: DefKind) (keyword keywordTwin: Comments) (name nameTwin: Word)
    (names: WordsAlike name nameTwin) (forallKeyword forallTwin: Option Word)
    (foralls: Option.Alike WordsAlike forallKeyword forallTwin) (params paramsTwin: List Group)
    (paramses: List.All2 GroupsAlike params paramsTwin)
    (colon colonTwin: Comments) (result resultTwin: Expr)
    (results: ExprsAlike result resultTwin) (decreasingClause decreasingTwin: Option (Comments, Expr))
    (decreasings: Option.Alike (PairAlike Anything ExprsAlike) decreasingClause decreasingTwin)
    (unfoldingClause unfoldingTwin: Option (Comments, List Word))
    (unfoldings: Option.Alike (PairAlike Anything (List.All2 WordsAlike)) unfoldingClause unfoldingTwin):
    HeaderAlike {
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
    }
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
        decreasingClause = decreasingTwin,
        unfoldingClause = unfoldingTwin
      } :=
  calc walkHeader blankPure
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
      decreasingClause,
      unfoldingClause
    }
    _ = {
        exportKeyword = blankComments exportKeyword,
        opaqueKeyword = blankComments opaqueKeyword,
        kind,
        keyword = Comments.none,
        name = name.blank,
        forallKeyword = forallKeyword.map Word.blank,
        params = blankGroups (walkGroups blankPure params),
        colon = Comments.none,
        result = result.walk blankPure,
        decreasingClause = blankAfter (walkAfter blankPure decreasingClause),
        unfoldingClause = blankUnfolding unfoldingClause
      } := byComputing
    _ = {
        exportKeyword = blankComments exportTwin,
        opaqueKeyword = blankComments opaqueTwin,
        kind,
        keyword = Comments.none,
        name = nameTwin.blank,
        forallKeyword = forallTwin.map Word.blank,
        params = blankGroups (walkGroups blankPure paramsTwin),
        colon = Comments.none,
        result = resultTwin.walk blankPure,
        decreasingClause = blankAfter (walkAfter blankPure decreasingTwin),
        unfoldingClause = blankUnfolding unfoldingTwin
      } :=
      rewrite commentsBlankAlike exportKeyword exportTwin exports,
          commentsBlankAlike opaqueKeyword opaqueTwin opaques,
          names,
          keywordBlank forallKeyword forallTwin foralls,
          groupsBlankAlike params paramsTwin paramses,
          results,
          afterAlike decreasingClause decreasingTwin decreasings,
          unfoldingBlankAlike unfoldingClause unfoldingTwin unfoldings
    _ = walkHeader blankPure {
        exportKeyword = exportTwin,
        opaqueKeyword = opaqueTwin,
        kind,
        keyword = keywordTwin,
        name = nameTwin,
        forallKeyword = forallTwin,
        params = paramsTwin,
        colon = colonTwin,
        result = resultTwin,
        decreasingClause = decreasingTwin,
        unfoldingClause = unfoldingTwin
      } := byComputing

theorem alikePrimitive: DefBodyAlike Primitive Primitive := byComputing

theorem alikeAssigned ∀ (colonEq colonEqTwin: Comments) (value valueTwin: Expr)
    (values: ExprsAlike value valueTwin):
    DefBodyAlike (Assigned colonEq value) (Assigned colonEqTwin valueTwin) :=
  calc (walkDefBody blankPure (Assigned colonEq value)).blank
    _ = Assigned Comments.none (value.walk blankPure) := byComputing
    _ = Assigned Comments.none (valueTwin.walk blankPure) := rewrite values
    _ = (walkDefBody blankPure (Assigned colonEqTwin valueTwin)).blank := byComputing

theorem alikeArms ∀ (arms twins: List Arm)
    (alike: List.All2 ArmAlike arms twins):
    DefBodyAlike (Arms arms) (Arms twins) :=
  calc (walkDefBody blankPure (Arms arms)).blank
    _ = Arms (blankArms (walkArms blankPure arms)) := byComputing
    _ = Arms (blankArms (walkArms blankPure twins)) := rewrite armsBlank arms twins alike
    _ = (walkDefBody blankPure (Arms twins)).blank := byComputing

theorem alikeDefinition ∀ (attributes twinAttributes: List Attributes)
    (attributeses: List.All2 AttributeGroupAlike attributes twinAttributes) (header twin: Header)
    (headers: HeaderAlike header twin) (body bodyTwin: DefBody)
    (bodies: DefBodyAlike body bodyTwin):
    DeclsAlike (Definition attributes header body) (Definition twinAttributes twin bodyTwin) :=
  calc (Definition attributes header body).walk blankPure
    _ = Definition
        (walkAttributes blankPure attributes)
        (walkHeader blankPure header)
        (walkDefBody blankPure body).blank := byComputing
    _ = Definition
        (walkAttributes blankPure twinAttributes)
        (walkHeader blankPure twin)
        (walkDefBody blankPure bodyTwin).blank :=
      rewrite walkAttributesAlike attributes twinAttributes attributeses, headers, bodies
    _ = (Definition twinAttributes twin bodyTwin).walk blankPure := byComputing

theorem followsDefKindOf ∀ (modes: Modes):
    Parse.Follows SameCode Same (() => defKindOf modes) (() => defKindOf modes) :=
  byWalking []

theorem followsDefinitionName ∀ (modes: Modes):
    Parse.Follows SameCode WordsAlike (() => definitionName modes) (() => definitionName modes) :=
  followsThenEq (followsAt modes Upper) (upper =>
    match upper with
      | True => followsUpperQualified modes "a name"
      | False => followsLowerQualified modes "a name")

theorem followsForallEnd ∀ (modes: Modes) (word twin: Word)
    (words: WordsAlike word twin) (paren bracket: Bool):
    Parse.Follows SameCode (Option.Alike WordsAlike) (() => forallEnd modes word paren bracket) (() =>
      forallEnd modes twin paren bracket) :=
  byWalking [followsFail]

theorem followsForallBump ∀ (modes: Modes):
    Parse.Follows SameCode (Option.Alike WordsAlike) (() => forallBump modes) (() => forallBump modes) :=
  byWalking [followsForallEnd]

theorem followsForallAt ∀ (modes: Modes) (kind: DefKind) (found: Bool):
    Parse.Follows SameCode (Option.Alike WordsAlike) (() => forallAt modes kind found) (() =>
      forallAt modes kind found) :=
  byWalking [followsFatalAny, followsForallBump]

theorem followsForallPart ∀ (modes: Modes) (kind: DefKind):
    Parse.Follows SameCode (Option.Alike WordsAlike) (() => forallPart modes kind) (() => forallPart modes kind) :=
  byWalking [followsForallAt]

theorem followsHeaderParamStep ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (modes: Modes) (atColon: Bool):
    Parse.Follows SameCode (Option.Alike GroupsAlike) (() => headerParamStep self modes atColon) (() =>
      headerParamStep selfTwin modes atColon) :=
  byWalking [followsHeaderGroup knot modes GroupParam None]

theorem followsHeaderParams ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin) (modes: Modes):
    Parse.Follows SameCode (List.All2 GroupsAlike) (() => headerParams self modes) (() =>
      headerParams selfTwin modes) :=
  Parse.followsLoop (followsThenEq (followsAt modes Colon) (atColon => followsHeaderParamStep knot modes atColon))

-- The clauses after the result type.

theorem followsAllowColonEq ∀ (modes: Modes):
    Parse.Follows SameCode Same (() => allowColonEq modes) (() => allowColonEq modes) :=
  followsLook (allowColonEqOn modes) (allowColonEqOnDeaf modes)

theorem followsDecreasingClauseOf ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin) (headerModes: Modes):
    Parse.Follows SameCode
      (Option.Alike (PairAlike Anything ExprsAlike))
      (() => decreasingClauseOf self headerModes)
      (() => decreasingClauseOf selfTwin headerModes) :=
  byWalking [followsFixedFrom]

theorem followsDecreasingAt ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (headerModes: Modes) (isInstance found: Bool):
    Parse.Follows SameCode
      (Option.Alike (PairAlike Anything ExprsAlike))
      (() => decreasingAt self headerModes isInstance found)
      (() => decreasingAt selfTwin headerModes isInstance found) :=
  byWalking [followsFatalAny, followsDecreasingClauseOf knot]

theorem followsDecreasingPart ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (modes headerModes: Modes) (isInstance: Bool):
    Parse.Follows SameCode
      (Option.Alike (PairAlike Anything ExprsAlike))
      (() => decreasingPart self modes headerModes isInstance)
      (() => decreasingPart selfTwin modes headerModes isInstance) :=
  byWalking [followsDecreasingAt knot]

theorem followsAfterDecreasingOf ∀ (modes: Modes) (clause clauseTwin: Option (Comments, Expr))
    (clauses: Option.Alike (PairAlike Anything ExprsAlike) clause clauseTwin):
    Parse.Follows SameCode Same (() => afterDecreasingOf modes clause) (() => afterDecreasingOf modes clauseTwin) :=
  let same: clause.isSome = clauseTwin.isSome := optionIsSome clause clauseTwin clauses
  rewrite same then
    match clauseTwin.isSome with
      | True => followsAllowColonEq modes
      | False => Parse.followsDone byComputing

def UnfoldingNamesFollow (modes: Modes) (fuel: Nat): Prop :=
  ∀ (found twin: List Word) => List.All2 WordsAlike found twin
    → Parse.Follows SameCode (List.All2 WordsAlike) (() => unfoldingNames fuel modes found) (() =>
      unfoldingNames fuel modes twin)

theorem followsUnfoldingName ∀ (modes: Modes) (upper: Bool):
    Parse.Follows SameCode WordsAlike (() => unfoldingName modes upper) (() => unfoldingName modes upper) :=
  byWalking [followsUpperQualified, followsLowerQualified]

theorem followsUnfoldingNext ∀ (more: Nat) (modes: Modes)
    (again: UnfoldingNamesFollow modes more) (found twins: List Word)
    (founds: List.All2 WordsAlike found twins) (name nameTwin: Word)
    (names: WordsAlike name nameTwin) (comma: Bool):
    Parse.Follows SameCode (List.All2 WordsAlike) (() => unfoldingNext more modes found name comma) (() =>
      unfoldingNext more modes twins nameTwin comma) :=
  byWalking [] then (List.all2Reverse [name, ..found] [nameTwin, ..twins] (Both names founds))

theorem followsUnfoldingNames ∀ (fuel: Nat) (modes: Modes) (found twins: List Word)
    (founds: List.All2 WordsAlike found twins):
    Parse.Follows SameCode (List.All2 WordsAlike) (() => unfoldingNames fuel modes found) (() =>
      unfoldingNames fuel modes twins) :=
  match fuel with
    | Succ more => followsThenEq (followsAt modes Upper) (upper =>
      Parse.followsThen (followsUnfoldingName modes upper) (name nameTwin names =>
        followsThenEq (followsAt modes Comma) (comma =>
          followsUnfoldingNext more modes
            (again twinsAgain agains => followsUnfoldingNames more modes again twinsAgain agains)
            found
            twins
            founds
            name
            nameTwin
            names
            comma)))
    | Zero => Parse.followsDone (List.all2Reverse found twins founds)

theorem followsUnfoldingClauseOf ∀ (afterDecreasing: Modes):
    Parse.Follows SameCode
      (Option.Alike (PairAlike Anything (List.All2 WordsAlike)))
      (() => unfoldingClauseOf afterDecreasing)
      (() => unfoldingClauseOf afterDecreasing) :=
  Parse.followsThen followsFixedFrom (keyword keywordTwin keywords =>
    followsFuel
      (fuel => (let names := unfoldingNames fuel afterDecreasing []; Some (keyword, names)))
      (fuel => (let names := unfoldingNames fuel afterDecreasing []; Some (keywordTwin, names)))
      (fuel =>
        Parse.followsMap
          (names => Some (keyword, names))
          (names => Some (keywordTwin, names))
          (followsUnfoldingNames fuel afterDecreasing [] [] Trivial)
          (names namesTwin nameses => (keywords, nameses))))

theorem followsUnfoldingAt ∀ (afterDecreasing: Modes) (isInstance found: Bool):
    Parse.Follows SameCode
      (Option.Alike (PairAlike Anything (List.All2 WordsAlike)))
      (() => unfoldingAt afterDecreasing isInstance found)
      (() => unfoldingAt afterDecreasing isInstance found) :=
  match found with
    | True =>
      match isInstance with
        | True => followsFatalAny _ (() => Syntax.fatal "an instance can't have `unfolding`")
        | False => followsUnfoldingClauseOf afterDecreasing
    | False => Parse.followsDone Trivial

theorem followsUnfoldingPart ∀ (modes afterDecreasing: Modes) (isInstance: Bool):
    Parse.Follows SameCode
      (Option.Alike (PairAlike Anything (List.All2 WordsAlike)))
      (() => unfoldingPart modes afterDecreasing isInstance)
      (() => unfoldingPart modes afterDecreasing isInstance) :=
  byWalking [followsUnfoldingAt]

theorem followsAfterUnfoldingOf ∀ (afterDecreasing: Modes) (clause clauseTwin: Option (Comments, List Word))
    (clauses: Option.Alike (PairAlike Anything (List.All2 WordsAlike)) clause clauseTwin):
    Parse.Follows SameCode Same (() => afterUnfoldingOf afterDecreasing clause) (() =>
      afterUnfoldingOf afterDecreasing clauseTwin) :=
  let same: clause.isSome = clauseTwin.isSome := optionIsSome clause clauseTwin clauses
  rewrite same then
    match clauseTwin.isSome with
      | True => followsAllowColonEq afterDecreasing
      | False => Parse.followsDone byComputing

theorem followsClauseConflict ∀ (afterUnfolding: Modes) (clause clauseTwin: Option (Comments, List Word))
    (clauses: Option.Alike (PairAlike Anything (List.All2 WordsAlike)) clause clauseTwin):
    Parse.Follows SameCode Same (() => clauseConflict afterUnfolding clause) (() =>
      clauseConflict afterUnfolding clauseTwin) :=
  let same: clause.isSome = clauseTwin.isSome := optionIsSome clause clauseTwin clauses
  followsThenEq (followsAt afterUnfolding KwDecreasing) (found =>
    let conflict: conflictOn found clause = conflictOn found clauseTwin := Eq.cong (some => found && some) same
    Parse.followsDone conflict)

theorem followsBodyModesOf ∀ (afterUnfolding: Modes) (isInstance: Bool) (local: Option Nat):
    Parse.Follows SameCode Same (() => bodyModesOf afterUnfolding isInstance local) (() =>
      bodyModesOf afterUnfolding isInstance local) :=
  byWalking [followsAtEither]

-- Definition bodies.

theorem followsAssignedEnd ∀ (colonEq colonEqTwin: Comments) (value valueTwin: Expr)
    (values: ExprsAlike value valueTwin) (arms: Bool):
    Parse.Follows SameCode DefBodyAlike (() => assignedEnd colonEq value arms) (() =>
      assignedEnd colonEqTwin valueTwin arms) :=
  byWalking [followsFatalAny] then (alikeAssigned colonEq colonEqTwin value valueTwin values)

theorem followsAssignedValue ∀ (modes: Modes) (colonEq colonEqTwin: Comments) (value valueTwin: Expr)
    (values: ExprsAlike value valueTwin):
    Parse.Follows SameCode DefBodyAlike (() => assignedValue modes colonEq value) (() =>
      assignedValue modes colonEqTwin valueTwin) :=
  byWalking [followsAssignedEnd]

theorem followsAssignedBody ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin) (modes: Modes):
    Parse.Follows SameCode DefBodyAlike (() => assignedBody self modes) (() => assignedBody selfTwin modes) :=
  byWalking [followsFixedFrom, followsAssignedValue]

theorem refusalBody ∀ (isInstance: Bool) (body twin: DefBody)
    (bodies: DefBodyAlike body twin) (items: List Item):
    definitionRefusal isInstance body items = definitionRefusal isInstance twin items :=
  match body, twin with
    | Primitive, Primitive => byComputing
    | Assigned a b, Assigned c d => byComputing
    | Arms x, Arms y => byComputing

theorem followsDefinitionWhere ∀ (isInstance: Bool) (body twin: DefBody)
    (bodies: DefBodyAlike body twin) (items others: List Item)
    (same: List.All2 SameCode items others):
    Parse.Follows SameCode DefBodyAlike (() => definitionWhere isInstance body items) (() =>
      definitionWhere isInstance twin others) :=
  let first: definitionRefusal isInstance body items = definitionRefusal isInstance body others :=
    deafOfStripped (definitionRefusal isInstance body) (definitionRefusalDeaf isInstance body) items others same
  rewrite first, refusalBody isInstance body twin bodies others then
    match definitionRefusal isInstance twin others with
      | Some message => followsFatalAny _ (() => Syntax.fatal message)
      | None => Parse.followsDone bodies

theorem followsDefinitionChecked ∀ (isInstance: Bool) (body twin: DefBody)
    (bodies: DefBodyAlike body twin):
    Parse.Follows SameCode DefBodyAlike (() => definitionChecked isInstance body) (() =>
      definitionChecked isInstance twin) :=
  byWalking [followsDefinitionWhere]
