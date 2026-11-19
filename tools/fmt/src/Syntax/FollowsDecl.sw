--| Two runs of the parser on items that differ only in their comments give alike trees (docs/reviews/
--| SW-4132-two-run-parse.md, lane 6): `followsF`, one lemma for each parser function of `Syntax/DeclParser.sw`, says
--| that `F` follows itself on alike arguments, by the pattern of `Syntax/FollowsBase.sw`.
--|
--| Covered (DeclParser.sw, in the order of the file):
--|
--| - fixed tokens and attributes: `fixedFrom`, `Modes.expectFixed`, `attributesOf`, `attributeGroups`, `attributeGroupStep`,
--|   `attributeGroupAt`, `attributeGroup`, `attributeGroupEnd`, `attributeItems`, `attributeItemsAt`, `attributeItem`,
--|   `attributeArgument`, `attributeArgumentOn`, `attributeNext`, `attributeParts`, `attributePart`, `refuseAttributes`,
--|   `Modes.lowerQualified`(`On`), `Modes.upperQualified`(`On`), `Modes.upper`;
--| - headers' parameter groups, with the `bare` flag: `headerGroup`, `headerGroupSeen`, `headerGroupOn`,
--|   `headerGroupParts`, `headerGroupNames`, `headerGroupAuto`, `headerGroupTyped`, `headerGroupNamed`,
--|   `headerGroupColon`, `headerDefault`, `headerGroupEnd`, `consumedBare`, `paramName`(`On`), `paramNames`,
--|   `paramNameStep`, `lowerNames`, `lowerNameStep`;
--| - binders and types: `binderGroup`, `binderDefault`, `implicitBinder`, `implicitBinderOf`, `implicitNamed`,
--|   `allowBrace`, `binderType`, `binderTypeSeen`, `binderTypeOn`, `resultType`, `resultAllowed`, `rowAhead`,
--|   `resultRow`, `effectResult`, `rowOf`, `rowStart`, `rowAbilities`, `rowVariable`, `rowPart`, `rowClose`,
--|   `piBinder`, `piExpr`;
--| - definitions: `definitionParts`, `defKindOf`, `definitionName`, `forallPart`, `forallAt`, `forallBump`,
--|   `forallEnd`, `headerParams`, `headerParamStep`, `decreasingPart`, `decreasingAt`, `decreasingClauseOf`,
--|   `afterDecreasingOf`, `unfoldingPart`, `unfoldingAt`, `unfoldingClauseOf`, `unfoldingNames`, `unfoldingName`,
--|   `unfoldingNext`, `afterUnfoldingOf`, `clauseConflict`, `allowColonEq`, `bodyModesOf`, `definitionBody`,
--|   `definitionBodyOn`, `assignedBody`, `assignedValue`, `assignedEnd`, `armsBody`, `definitionArms`,
--|   `definitionArmsOn`, `definitionArmsFrom`, `definitionArmStep`, `definitionArm`, `definitionChecked`,
--|   `definitionWhere`, `definition`, `instanceDecl`;
--| - data types, interfaces, abilities, tests, rule sets: `dataDecl`, `dataDeclOn`, `dataName`, `dataParams`,
--|   `dataParamStep`, `dataParamBracket`, `dataParamLeft`, `dataIndicesPart`, `dataIndices`, `dataIndexAt`,
--|   `dataIndexNext`, `typeSynonym`, `typeDecl`, `typeBody`, `typeAfterEquals`, `typeBraced`, `interfaceDecl`,
--|   `interfaceFields`, `bracedFields`, `bracedFieldsIn`, `fieldsFrom`, `fieldsAt`, `fieldDefault`, `fieldsNext`,
--|   `constructorsOf`, `constructorsAt`, `constructorStep`, `constructorResult`, `constructorParts`,
--|   `constructorBraced`, `constructorParen`, `constructorBracket`, `abilityDecl`, `abilityOn`, `abilityParams`,
--|   `abilityParamStep`, `operation`, `operations`, `operationNext`, `testDecl`, `testName`, `testAfterName`,
--|   `ruleSetDecl`, `ruleSetName`, `ruleSetAfterName`, `ruleSetOpen`, `ruleSetOrMissing`;
--| - namespace lines and imports: `namespaceLine`, `namespaceAfter`, `importLine`, `importPath`, `importAfter`,
--|   `importOpen`, `importedOf`, `importAllEnd`, `importNames`, `importClose`, `importItems`, `importItemsOn`,
--|   `importStop`, `importNamed`, `importTail`, `importAlias`, `importAliasOn`, `importAliasWord`;
--| - one declaration: `declaration`, `declarationAttributes`, `declarationRefusal`, `declarationKind`,
--|   `namespaceStep`, `importStep`, `declarationFinish`, `declarationEnd`, `declarationBody`, `declarationBodyOn`,
--|   `declarationOther`, `exportAfter`, `exportPlain`, `afterOpaque`, `afterOpaqueOn`.
--|
--| Not covered: `expressionAt` is the knot (`expressionKnot`, from the rule lemma `ExpressionRule` that lane 8 proves);
--| the pure functions (`Seen`, `attributesRefused`, `ranOutOn`, `typeStarts`, `autoSplit`, `implicitAuto`, `isEquation`,
--| ...) have lane 2's `…Deaf` facts or local alike lemmas; `ranOutAtLine` and `fixedFrom` are lane 5's
--| (`FollowsForms`); and the file's loop, `parseFile`, `parseFileGroups`, `parseGroups`, `groupsOf` and `splitFrom`,
--| which run `Parse.run` over each group's items, belong to lane 8 (`Parse.followsRun`).
--|
--| Hypotheses. Each lemma takes the knot (`SelfFollows self selfTwin`, or `ExpressionRule` for the functions that
--| start a recursion with `expressionAt`) and alike arguments. Of other lanes' functions it uses, directly as lemmas
--| (nothing here is called from their files): `followsFull`, `followsGuardOf`, `followsArmBody`, `alikeArm`, `armsBlank`,
--| `followsWordAhead`, `followsRuleSet` (lanes 5 and 7). The only hypothesis a lane-5 function still needs is
--| `AltPatternFollows` (`followsArmPatterns`), taken by the lemmas that read arms. The closing section proves the
--| facts the other lanes assume of this file: `ResultTypeFollows` (lane 4), `HeaderGroupFollows`, `BinderTypeFollows`,
--| `PiExprFollows` (lane 5), `ExpectFixedFollows`, `LowerQualifiedFollows`, `AttributesOfFollows` and
--| `DefinitionPartsFollows` (lane 7).
--|
--| The `bare` flag (hard spot 1). `consumedBare`'s `Bool` is the one value read from comments; `followsConsumedBare`
--| relates it by `Anything`, `followsHeaderGroupEnd` takes the two runs' `consumed` flags unrelated, and `alikeGroup`
--| takes `bare` and `bareTwin` unrelated, because `Group.blank` sets `bare = True`. `Anything` also relates the `()`
--| results of `refuseAttributes`, `afterOpaque` and `afterOpaqueOn`, which compute nothing. No other `Bool` is related
--| by `Anything`.
--|
--| Relations (this file's own): `AttributeAlike`, `AttributeGroupAlike` (one group of attributes; lane 7's
--| `AttributesAlike` is the list), `RowsAlike`, `HeaderAlike`, `DefBodyAlike`, `ImportItemAlike`, `ImportedAlike`,
--| `OperationAlike`, `IndexStepAlike`, `IndicesAlike`, `FieldAlike`, `FieldsAlike`, `PartAlike`, `ConstructorAlike`,
--| `DataBodyAlike`; each is equality of the node walked with `blankPure` and blanked, via a `…Key` function.

namespace Syntax.FollowsDecl
import Std (Bool, DecEq, Eq, List, Nat, Option, Pair, Parse, Result, Text, Unit, Void)
import Syntax (..)
import Fmt (..)
import Fmt.Walk (..)
import Fmt.Proofs (blankPure)
import Syntax.DeafProofs (..)
import Syntax.FollowsBase (..)
import Syntax.FollowsLadder (..)
import Syntax.FollowsForms (..)
import Syntax.FollowsStatements (..)

-- Reading a fixed token: its comments are not compared.

theorem followsExpectFixed ∀ (modes: Modes) (wanted: Tok) (what: Text):
    Parse.Follows SameCode Anything (() => modes.expectFixed wanted what) (() => modes.expectFixed wanted what) :=
  Parse.followsThen (followsExpect modes wanted what) (found twin alike =>
    Parse.followsDone found.comments twin.comments Trivial)

-- A step that reads the number of items left to make fuel.

theorem followsFuel ∀ [alike: a → b → Prop] (k: Nat → {Parse Item} a) (kTwin: Nat → {Parse Item} b)
    (each: ∀ (fuel: Nat) => Parse.Follows SameCode alike (() => k fuel) (() => kTwin fuel)):
    Parse.Follows SameCode alike (() => k (Parse.mark().left + 1)) (() => kTwin (Parse.mark().left + 1)) :=
  Parse.followsThen Parse.followsMark (here hereTwin marks => rewrite marks.right.right then each (hereTwin.left + 1))

-- Relations.

def attributeBlank (attribute: Attribute): Attribute := {
  name = attribute.name.blank,
  parts = blankDottedParts attribute.parts,
  argument = attribute.argument.map Word.blank
}

def AttributeAlike (attribute twin: Attribute): Prop := attributeBlank attribute = attributeBlank twin

def AttributeGroupAlike (attributes twin: Attributes): Prop := blankAttributes attributes = blankAttributes twin

theorem dottedAlike ∀ (parts twins: List (Comments, Word))
    (alike: List.All2 (PairAlike Anything WordsAlike) parts twins):
    blankDottedParts parts = blankDottedParts twins :=
  match parts, twins with
    | [], [] => byComputing
    | [(written, part), ..rest], [(writtenTwin, partTwin), ..restTwin] =>
      let (head, tail) := alike
      let sameWord: part.blank = partTwin.blank := head.right
      calc blankDottedParts [(written, part), ..rest]
        _ = [(Comments.none, part.blank), ..blankDottedParts rest] := byComputing
        _ = [(Comments.none, partTwin.blank), ..blankDottedParts restTwin] :=
          rewrite sameWord, dottedAlike rest restTwin tail
        _ = blankDottedParts [(writtenTwin, partTwin), ..restTwin] := byComputing

theorem alikeAttribute ∀ (name nameTwin: Word)
    (names: WordsAlike name nameTwin) (parts partsTwin: List (Comments, Word))
    (partses: List.All2 (PairAlike Anything WordsAlike) parts partsTwin) (argument argumentTwin: Option Word)
    (arguments: Option.Alike WordsAlike argument argumentTwin):
    AttributeAlike { name, parts, argument } { name = nameTwin, parts = partsTwin, argument = argumentTwin } :=
  calc attributeBlank { name, parts, argument }
    _ = { name = name.blank, parts = blankDottedParts parts, argument = argument.map Word.blank } := byComputing
    _ = { name = nameTwin.blank, parts = blankDottedParts partsTwin, argument = argumentTwin.map Word.blank } :=
      rewrite names, dottedAlike parts partsTwin partses, keywordBlank argument argumentTwin arguments
    _ = attributeBlank { name = nameTwin, parts = partsTwin, argument = argumentTwin } := byComputing

theorem attributeItemsCons ∀ (item: Attribute) (rest: List Attribute):
    blankAttributeItems [item, ..rest] = [attributeBlank item, ..blankAttributeItems rest] :=
  match item with | { name, parts, argument } => byComputing

theorem attributeItemsAlike ∀ (items twins: List Attribute)
    (alike: List.All2 AttributeAlike items twins):
    blankAttributeItems items = blankAttributeItems twins :=
  match items, twins with
    | [], [] => byComputing
    | [item, ..rest], [twin, ..restTwin] =>
      let (head, tail) := alike
      calc blankAttributeItems [item, ..rest]
        _ = [attributeBlank item, ..blankAttributeItems rest] := attributeItemsCons item rest
        _ = [attributeBlank twin, ..blankAttributeItems restTwin] :=
          rewrite head, attributeItemsAlike rest restTwin tail
        _ = blankAttributeItems [twin, ..restTwin] := Eq.flipped (attributeItemsCons twin restTwin)

theorem alikeAttributes ∀ (at atTwin open openTwin: Comments) (items twins: List Attribute)
    (alike: List.All2 AttributeAlike items twins) (trailing trailingTwin: Bool)
    (trailings: trailing = trailingTwin) (close closeTwin: Comments):
    AttributeGroupAlike { at, open, items, trailingComma = trailing, close } {
      at = atTwin,
      open = openTwin,
      items = twins,
      trailingComma = trailingTwin,
      close = closeTwin
    } :=
  calc blankAttributes { at, open, items, trailingComma = trailing, close }
    _ = {
        at = Comments.none,
        open = Comments.none,
        items = blankAttributeItems items,
        trailingComma = trailing,
        close = Comments.none
      } := byComputing
    _ = {
        at = Comments.none,
        open = Comments.none,
        items = blankAttributeItems twins,
        trailingComma = trailingTwin,
        close = Comments.none
      } := rewrite attributeItemsAlike items twins alike, trailings
    _ = blankAttributes {
        at = atTwin,
        open = openTwin,
        items = twins,
        trailingComma = trailingTwin,
        close = closeTwin
      } := byComputing

theorem walkAttributesAlike ∀ (items twins: List Attributes)
    (alike: List.All2 AttributeGroupAlike items twins):
    walkAttributes blankPure items = walkAttributes blankPure twins :=
  match items, twins with
    | [], [] => byComputing
    | [x, ..xs], [y, ..ys] =>
      let (head, tail) := alike
      calc walkAttributes blankPure [x, ..xs]
        _ = [blankAttributes x, ..walkAttributes blankPure xs] := byComputing
        _ = [blankAttributes y, ..walkAttributes blankPure ys] := rewrite head, walkAttributesAlike xs ys tail
        _ = walkAttributes blankPure [y, ..ys] := byComputing

-- Attributes.

theorem followsLowerQualifiedOn ∀ (modes: Modes) (what: Text) (seen: Option Tok):
    Parse.Follows SameCode WordsAlike (() => modes.lowerQualifiedOn what seen) (() =>
      modes.lowerQualifiedOn what seen) :=
  match isSome Lower seen with
    | True => followsBump
    | False => followsFailName modes what (() => modes.failName what)

theorem followsLowerQualified ∀ (modes: Modes) (what: Text):
    Parse.Follows SameCode WordsAlike (() => modes.lowerQualified what) (() => modes.lowerQualified what) :=
  followsPeeked modes (seen => modes.lowerQualifiedOn what seen) (seen => modes.lowerQualifiedOn what seen) (seen =>
    followsLowerQualifiedOn modes what seen)

theorem followsUpperQualifiedOn ∀ (modes: Modes) (what: Text) (seen: Option Tok):
    Parse.Follows SameCode WordsAlike (() => modes.upperQualifiedOn what seen) (() =>
      modes.upperQualifiedOn what seen) :=
  match isSome Upper seen with
    | True => followsBump
    | False => followsFail modes what (() => modes.fail what)

theorem followsUpperQualified ∀ (modes: Modes) (what: Text):
    Parse.Follows SameCode WordsAlike (() => modes.upperQualified what) (() => modes.upperQualified what) :=
  followsPeeked modes (seen => modes.upperQualifiedOn what seen) (seen => modes.upperQualifiedOn what seen) (seen =>
    followsUpperQualifiedOn modes what seen)

theorem followsUpper ∀ (modes: Modes) (what: Text):
    Parse.Follows SameCode WordsAlike (() => modes.upper what) (() => modes.upper what) :=
  Parse.followsThen (followsUpperQualified modes what) (name nameTwin names =>
    rewrite wordTextSame name nameTwin names then
      match nameTwin.text.contains "." with
        | True => followsFatalAny _ _
        | False => Parse.followsDone name nameTwin names)

theorem followsRefuseAttributes ∀ (attributes twins: List Attributes)
    (alike: List.All2 AttributeGroupAlike attributes twins) (what: Text):
    Parse.Follows SameCode Anything (() => refuseAttributes attributes what) (() => refuseAttributes twins what) :=
  match attributes, twins with
    | [], [] => Parse.followsDone () () Trivial
    | [x, ..xs], [y, ..ys] => followsFatalAny _ _

theorem followsAttributeArgumentOn ∀ (modes: Modes) (seen: Option Tok):
    Parse.Follows SameCode (Option.Alike WordsAlike) (() => attributeArgumentOn modes seen) (() =>
      attributeArgumentOn modes seen) :=
  match isSome Str seen with
    | True =>
      Parse.followsMap
        [alike := Option.Alike WordsAlike]
        [p := () => bump()]
        [q := () => bump()]
        (word => Some word)
        (word => Some word)
        (x y alike => alike)
        followsBump
    | False =>
      match isSome StrStart seen with
        | True => followsFatalAny _ (() => Syntax.fatal "an attribute's argument is a plain string, without `\${…}`")
        | False => Parse.followsDone None None Trivial

theorem followsAttributeArgument ∀ (modes: Modes):
    Parse.Follows SameCode (Option.Alike WordsAlike) (() => attributeArgument modes) (() => attributeArgument modes) :=
  followsPeeked modes (seen => attributeArgumentOn modes seen) (seen => attributeArgumentOn modes seen) (seen =>
    followsAttributeArgumentOn modes seen)

theorem followsAttributePart ∀ (modes: Modes) (dot: Bool):
    Parse.Follows SameCode (Option.Alike (PairAlike Anything WordsAlike)) (() => attributePart modes dot) (() =>
      attributePart modes dot) :=
  match dot with
    | True => Parse.followsThen followsFixedFrom (written writtenTwin writtens =>
      Parse.followsMap
        (part => Some (written, part))
        (part => Some (writtenTwin, part))
        (part partTwin parts => (writtens, parts))
        (followsLowerQualified modes "the rest of the attribute's name"))
    | False => Parse.followsDone None None Trivial

theorem followsAttributeParts ∀ (modes: Modes):
    Parse.Follows SameCode (List.All2 (PairAlike Anything WordsAlike)) (() => attributeParts modes) (() =>
      attributeParts modes) :=
  Parse.followsLoop _ _ (followsThenEq (followsAt modes Dot) (dot => followsAttributePart modes dot))

def AttributeItemsFollow (modes: Modes) (fuel: Nat): Prop :=
  ∀ (found twin: List Attribute) => List.All2 AttributeAlike found twin
    → Parse.Follows SameCode (PairAlike (List.All2 AttributeAlike) Same) (() => attributeItems fuel modes found) (() =>
      attributeItems fuel modes twin)

theorem followsAttributeNext ∀ (more: Nat) (modes: Modes)
    (again: AttributeItemsFollow modes more) (done twins: List Attribute)
    (dones: List.All2 AttributeAlike done twins) (comma: Bool):
    Parse.Follows SameCode
      (PairAlike (List.All2 AttributeAlike) Same)
      (() => attributeNext more modes done comma)
      (() => attributeNext more modes twins comma) :=
  match comma with
    | True => Parse.followsThen followsBump (found twin alike => again done twins dones)
    | False => Parse.followsDone _ _ (List.all2Reverse done twins dones, byComputing)

theorem followsAttributeItem ∀ (more: Nat) (modes: Modes)
    (again: AttributeItemsFollow modes more) (found twins: List Attribute)
    (founds: List.All2 AttributeAlike found twins):
    Parse.Follows SameCode (PairAlike (List.All2 AttributeAlike) Same) (() => attributeItem more modes found) (() =>
      attributeItem more modes twins) :=
  Parse.followsThen (followsLowerQualified modes "an attribute's name, such as `js.name`") (name nameTwin names =>
    Parse.followsThen (followsAttributeParts modes) (parts partsTwin partses =>
      Parse.followsThen (followsAttributeArgument modes) (value valueTwin values =>
        followsThenEq (followsAt modes Comma) (comma =>
          followsAttributeNext more modes again
            [{ name, parts, argument = value }, ..found]
            [{ name = nameTwin, parts = partsTwin, argument = valueTwin }, ..twins]
            (Both (alikeAttribute name nameTwin names parts partsTwin partses value valueTwin values) founds)
            comma))))

theorem followsAttributeItemsAt ∀ (more: Nat) (modes: Modes)
    (again: AttributeItemsFollow modes more) (found twins: List Attribute)
    (founds: List.All2 AttributeAlike found twins) (closed: Bool):
    Parse.Follows SameCode
      (PairAlike (List.All2 AttributeAlike) Same)
      (() => attributeItemsAt more modes found closed)
      (() => attributeItemsAt more modes twins closed) :=
  let empties: found.isEmpty = twins.isEmpty := List.all2IsEmpty found twins founds
  rewrite empties then
    match closed && !twins.isEmpty with
      | True =>
        Parse.followsDone (found.reverse, True) (twins.reverse, True) (List.all2Reverse found twins founds, byComputing)
      | False => followsAttributeItem more modes again found twins founds

theorem followsAttributeItems ∀ (fuel: Nat) (modes: Modes) (found twins: List Attribute)
    (founds: List.All2 AttributeAlike found twins):
    Parse.Follows SameCode (PairAlike (List.All2 AttributeAlike) Same) (() => attributeItems fuel modes found) (() =>
      attributeItems fuel modes twins) :=
  match fuel with
    | Succ more => followsThenEq (followsAt modes RBracket) (closed =>
      followsAttributeItemsAt more modes
        (again twin dones => followsAttributeItems more modes again twin dones)
        found
        twins
        founds
        closed)
    | Zero => Parse.followsDone _ _ (List.all2Reverse found twins founds, byComputing)

theorem followsAttributeGroupEnd ∀ (modes: Modes)
    (at atTwin open openTwin: Comments) (pair pairTwin: (List Attribute, Bool))
    (pairs: PairAlike (List.All2 AttributeAlike) Same pair pairTwin):
    Parse.Follows SameCode (Option.Alike AttributeGroupAlike) (() => attributeGroupEnd modes at open pair) (() =>
      attributeGroupEnd modes atTwin openTwin pairTwin) :=
  match pair, pairTwin with
    | (items, trailing), (itemsTwin, trailingTwin) =>
      Parse.followsMap
        [alike := Option.Alike AttributeGroupAlike]
        [p := () => modes.expectFixed RBracket "`,` or `]` after the attribute"]
        [q := () => modes.expectFixed RBracket "`,` or `]` after the attribute"]
        (close => Some { at, open, items, trailingComma = trailing, close })
        (close => Some { at = atTwin, open = openTwin, items = itemsTwin, trailingComma = trailingTwin, close })
        (close closeTwin closes =>
          alikeAttributes at atTwin open openTwin items itemsTwin pairs.left trailing trailingTwin pairs.right close
              closeTwin)
        (followsExpectFixed modes RBracket "`,` or `]` after the attribute")

theorem followsAttributeGroup ∀ (modes: Modes):
    Parse.Follows SameCode (Option.Alike AttributeGroupAlike) (() => attributeGroup modes) (() =>
      attributeGroup modes) :=
  Parse.followsThen followsFixedFrom (at atTwin ats =>
    Parse.followsThen (followsExpectFixed modes LBracket "`[`") (open openTwin opens =>
      Parse.followsThen Parse.followsMark (here hereTwin marks =>
        rewrite marks.right.right then
          Parse.followsThen (followsAttributeItems (hereTwin.left + 1) modes [] [] Trivial) (pair pairTwin pairs =>
            followsAttributeGroupEnd modes at atTwin open openTwin pair pairTwin pairs))))

theorem followsAttributeGroupAt ∀ (modes: Modes) (found: Bool):
    Parse.Follows SameCode (Option.Alike AttributeGroupAlike) (() => attributeGroupAt modes found) (() =>
      attributeGroupAt modes found) :=
  match found with
    | True => followsAttributeGroup modes
    | False => Parse.followsDone None None Trivial

theorem followsAttributeGroupStep ∀ (modes: Modes):
    Parse.Follows SameCode (Option.Alike AttributeGroupAlike) (() => attributeGroupStep modes) (() =>
      attributeGroupStep modes) :=
  followsThenEq (followsAt modes At) (found => followsAttributeGroupAt modes found)

theorem followsAttributeGroups ∀ (modes: Modes):
    Parse.Follows SameCode (List.All2 AttributeGroupAlike) (() => attributeGroups modes) (() =>
      attributeGroups modes) :=
  Parse.followsLoop _ _ (followsAttributeGroupStep modes)

theorem followsAttributesOf ∀ (modes: Modes):
    Parse.Follows SameCode (List.All2 AttributeGroupAlike) (() => attributesOf modes) (() => attributesOf modes) :=
  followsAttributeGroups modes

-- Groups.

theorem commentsBlankAlike ∀ (found twin: Option Comments)
    (alike: Option.Alike Anything found twin):
    blankComments found = blankComments twin :=
  match found, twin with
    | Some x, Some y => byComputing
    | None, None => byComputing

theorem afterAlike ∀ (found twin: Option (Comments, Expr))
    (alike: Option.Alike (PairAlike Anything ExprsAlike) found twin):
    blankAfter (walkAfter blankPure found) = blankAfter (walkAfter blankPure twin) :=
  match found, twin with
    | Some (c, x), Some (d, y) =>
      let same: x.walk blankPure = y.walk blankPure := alike.right
      calc blankAfter (walkAfter blankPure (Some (c, x)))
        _ = Some (Comments.none, x.walk blankPure) := byComputing
        _ = Some (Comments.none, y.walk blankPure) := rewrite same
        _ = blankAfter (walkAfter blankPure (Some (d, y))) := byComputing
    | None, None => byComputing

theorem alikeGroup ∀ (kind: GroupKind) (implicit: Bool)
    (open openTwin: Comments) (attributes twinAttributes: List Attributes)
    (attributeses: List.All2 AttributeGroupAlike attributes twinAttributes) (auto autoTwin: Option Comments)
    (autos: Option.Alike Anything auto autoTwin) (names twinNames: List Word)
    (nameses: List.All2 WordsAlike names twinNames) (colon colonTwin: Option Comments)
    (colons: Option.Alike Anything colon colonTwin) (annotation annotationTwin: Option Expr)
    (annotations: Option.Alike ExprsAlike annotation annotationTwin) (default defaultTwin: Option (Comments, Expr))
    (defaults: Option.Alike (PairAlike Anything ExprsAlike) default defaultTwin)
    (close closeTwin: Comments) (bare bareTwin: Bool):
    GroupsAlike { kind, implicit, open, attributes, auto, names, colon, annotation, default, close, bare } {
      kind,
      implicit,
      open = openTwin,
      attributes = twinAttributes,
      auto = autoTwin,
      names = twinNames,
      colon = colonTwin,
      annotation = annotationTwin,
      default = defaultTwin,
      close = closeTwin,
      bare = bareTwin
    } :=
  calc ({ kind, implicit, open, attributes, auto, names, colon, annotation, default, close, bare }: Group).walk
      blankPure
    |> .blank
    _ = {
        kind,
        implicit,
        open = Comments.none,
        attributes = walkAttributes blankPure attributes,
        auto = blankComments auto,
        names = blankWords names,
        colon = blankComments colon,
        annotation = walkOptional blankPure annotation,
        default = blankAfter (walkAfter blankPure default),
        close = Comments.none,
        bare = True
      } := byComputing
    _ = {
        kind,
        implicit,
        open = Comments.none,
        attributes = walkAttributes blankPure twinAttributes,
        auto = blankComments autoTwin,
        names = blankWords twinNames,
        colon = blankComments colonTwin,
        annotation = walkOptional blankPure annotationTwin,
        default = blankAfter (walkAfter blankPure defaultTwin),
        close = Comments.none,
        bare = True
      } :=
      rewrite walkAttributesAlike attributes twinAttributes attributeses,
          commentsBlankAlike auto autoTwin autos,
          namesBlank names twinNames nameses,
          commentsBlankAlike colon colonTwin colons,
          walkOptionalAlike annotation annotationTwin annotations,
          afterAlike default defaultTwin defaults
    _ = ({
            kind,
            implicit,
            open = openTwin,
            attributes = twinAttributes,
            auto = autoTwin,
            names = twinNames,
            colon = colonTwin,
            annotation = annotationTwin,
            default = defaultTwin,
            close = closeTwin,
            bare = bareTwin
          }: Group).walk blankPure
        |> .blank := byComputing

-- Parameter names.

theorem followsParamNameOn ∀ (modes: Modes) (seen: Option Tok):
    Parse.Follows SameCode WordsAlike (() => paramNameOn modes seen) (() => paramNameOn modes seen) :=
  match seen with
    | Some Upper | Some LParen | Some LBrace =>
      followsFail modes "a parameter's name" (() => modes.fail "a parameter's name")
    | _ => followsLower modes "a parameter's name"

theorem followsParamName ∀ (modes: Modes):
    Parse.Follows SameCode WordsAlike (() => paramName modes) (() => paramName modes) :=
  followsPeeked modes (seen => paramNameOn modes seen) (seen => paramNameOn modes seen) (seen =>
    followsParamNameOn modes seen)

theorem followsParamNameStep ∀ (modes: Modes) (atLower: Bool):
    Parse.Follows SameCode (Option.Alike WordsAlike) (() => paramNameStep modes atLower) (() =>
      paramNameStep modes atLower) :=
  match atLower with
    | True => Parse.followsMap (word => Some word) (word => Some word) (x y alike => alike) (followsParamName modes)
    | False => Parse.followsDone None None Trivial

theorem followsParamNames ∀ (modes: Modes):
    Parse.Follows SameCode (List.All2 WordsAlike) (() => paramNames modes) (() => paramNames modes) :=
  Parse.followsLoop _ _ (followsThenEq (followsAt modes Lower) (atLower => followsParamNameStep modes atLower))

theorem followsLowerNameStep ∀ (modes: Modes) (atLower: Bool):
    Parse.Follows SameCode (Option.Alike WordsAlike) (() => lowerNameStep modes atLower) (() =>
      lowerNameStep modes atLower) :=
  match atLower with
    | True =>
      Parse.followsMap (word => Some word) (word => Some word) (x y alike => alike) (followsLower modes "a name")
    | False => Parse.followsDone None None Trivial

theorem followsLowerNames ∀ (modes: Modes):
    Parse.Follows SameCode (List.All2 WordsAlike) (() => lowerNames modes) (() => lowerNames modes) :=
  Parse.followsLoop _ _ (followsThenEq (followsAt modes Lower) (atLower => followsLowerNameStep modes atLower))

-- A binder's type.

def skipsToType (items: List Item): Bool := match skipGroup [] items with
  | Some [next, .._] => typeStarts next.kind
  | _ => False

def binderTypeBrace (self: Goal → {Parse Item} Expr) (allowed: Modes) (flag: Bool): {Parse Item} Expr :=
  if flag then Syntax.fatal "an ability row can't be written in a parameter's type" else full self allowed

theorem skipsToTypeDeaf ∀ (items: List Item): skipsToType items = skipsToType (items.map Item.stripped) :=
  rewrite skipGroupDeaf [] items then match skipGroup [] items with | None | Some [] | Some [_, .._] => byComputing

theorem binderTypeBraceEq ∀ (self: Goal → {Parse Item} Expr) (allowed: Modes) (open: Item) (rest: List Item):
    binderTypeOn self allowed (Some LBrace) [open, ..rest]
      = binderTypeBrace self allowed (skipsToType [open, ..rest]) :=
  match skipGroup [] [open, ..rest] with
    | None | Some [] => byComputing
    | Some [next, ..more] =>
      match typeStarts next.kind with
        | True => byComputing
        | False => byComputing

theorem followsAllowBrace ∀ (modes: Modes):
    Parse.Follows SameCode Same (() => allowBrace modes) (() => allowBrace modes) :=
  followsLook (allowBraceOn modes) (allowBraceOnDeaf modes)

theorem followsBinderTypeOn ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (allowed: Modes) (seen: Option Tok) (items others: List Item)
    (same: List.All2 SameCode items others):
    Parse.Follows SameCode ExprsAlike (() => binderTypeOn self allowed seen items) (() =>
      binderTypeOn selfTwin allowed seen others) :=
  match seen with
    | Some LBrace =>
      match items, others with
        | [open, ..rest], [openTwin, ..restTwin] =>
          rewrite binderTypeBraceEq self allowed open rest,
              binderTypeBraceEq selfTwin allowed openTwin restTwin,
              deafOfStripped skipsToType skipsToTypeDeaf [open, ..rest] [openTwin, ..restTwin] same then
            match skipsToType [openTwin, ..restTwin] with
              | True => followsFatalAny _ _
              | False => followsFull knot allowed
        | [], [] => followsFull knot allowed
    | _ => followsFull knot allowed

theorem followsBinderTypeSeen ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (allowed: Modes) (seen: Option Tok):
    Parse.Follows SameCode ExprsAlike (() => binderTypeSeen self allowed seen) (() =>
      binderTypeSeen selfTwin allowed seen) :=
  followsOn
    (items => binderTypeOn self allowed seen items)
    (items => binderTypeOn selfTwin allowed seen items)
    (itemList others same => followsBinderTypeOn knot allowed seen itemList others same)

theorem followsBinderType ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin) (modes: Modes):
    Parse.Follows SameCode ExprsAlike (() => binderType self modes) (() => binderType selfTwin modes) :=
  followsThenEq (followsAllowBrace modes) (allowed =>
    followsPeeked allowed
      (seen => binderTypeSeen self allowed seen)
      (seen => binderTypeSeen selfTwin allowed seen)
      (seen => followsBinderTypeSeen knot allowed seen))

-- Header groups.

theorem followsExpectFixedTwo ∀ (modes: Modes) (wanted: Tok) (what whatTwin: Text):
    Parse.Follows SameCode Anything (() => modes.expectFixed wanted what) (() => modes.expectFixed wanted whatTwin) :=
  Parse.followsThen
    (followsThenEq (followsPeek modes) (seen =>
      match isSome wanted seen with
        | True => followsBump
        | False => followsFail modes what (() => modes.fail whatTwin)))
    (found twin alike => Parse.followsDone found.comments twin.comments Trivial)

theorem followsHeaderDefault ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (inner: Modes) (implicit atColonEq: Bool):
    Parse.Follows SameCode
      (Option.Alike (PairAlike Anything ExprsAlike))
      (() => headerDefault self inner implicit atColonEq)
      (() => headerDefault selfTwin inner implicit atColonEq) :=
  match atColonEq with
    | True =>
      match implicit with
        | True => followsFatalAny _ _
        | False => Parse.followsThen followsFixedFrom (colonEq colonEqTwin colonEqs =>
          Parse.followsMap
            (value => Some (colonEq, value))
            (value => Some (colonEqTwin, value))
            (value valueTwin values => (colonEqs, values))
            (followsFull knot inner))
    | False => Parse.followsDone None None Trivial

theorem followsConsumedBare ∀ (started startedTwin: Parse.Mark Item):
    Parse.Follows SameCode Anything (() => consumedBare started) (() => consumedBare startedTwin) :=
  Parse.followsThen Parse.followsMark (here hereTwin marks => Parse.followsDone _ _ Trivial)

theorem followsHeaderGroupEnd ∀ (kind: GroupKind) (implicit: Bool)
    (open openTwin: Comments) (auto autoTwin: Option Comments)
    (autos: Option.Alike Anything auto autoTwin) (named namedTwin: List Word)
    (nameds: List.All2 WordsAlike named namedTwin)
    (colon colonTwin: Comments) (annotation annotationTwin: Expr)
    (annotations: ExprsAlike annotation annotationTwin) (default defaultTwin: Option (Comments, Expr))
    (defaults: Option.Alike (PairAlike Anything ExprsAlike) default defaultTwin)
    (close closeTwin: Comments) (refused: Option Text) (consumed consumedTwin: Bool):
    Parse.Follows SameCode GroupsAlike
      (() => headerGroupEnd kind implicit open auto named colon annotation default close refused consumed)
      (() =>
        headerGroupEnd kind implicit openTwin autoTwin namedTwin colonTwin annotationTwin defaultTwin closeTwin refused
            consumedTwin) :=
  match refused, default, defaultTwin with
    | Some message, Some _, Some _ => followsFatalAny _ _
    | Some message, None, None =>
      Parse.followsDone _ _
        (alikeGroup kind implicit open openTwin [] [] Trivial auto autoTwin autos named namedTwin nameds
          (Some colon)
          (Some colonTwin)
          Trivial
          (Some annotation)
          (Some annotationTwin)
          annotations
          None
          None
          defaults
          close
          closeTwin
          (default.isNone && consumed)
          (defaultTwin.isNone && consumedTwin))
    | None, Some _, Some _ =>
      Parse.followsDone _ _
        (alikeGroup kind implicit open openTwin [] [] Trivial auto autoTwin autos named namedTwin nameds
          (Some colon)
          (Some colonTwin)
          Trivial
          (Some annotation)
          (Some annotationTwin)
          annotations
          default
          defaultTwin
          defaults
          close
          closeTwin
          (default.isNone && consumed)
          (defaultTwin.isNone && consumedTwin))
    | None, None, None =>
      Parse.followsDone _ _
        (alikeGroup kind implicit open openTwin [] [] Trivial auto autoTwin autos named namedTwin nameds
          (Some colon)
          (Some colonTwin)
          Trivial
          (Some annotation)
          (Some annotationTwin)
          annotations
          None
          None
          defaults
          close
          closeTwin
          (default.isNone && consumed)
          (defaultTwin.isNone && consumedTwin))

theorem followsHeaderGroupColon ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (inner: Modes) (kind: GroupKind) (refused: Option Text) (implicit: Bool) (started startedTwin: Parse.Mark Item)
    (open openTwin: Comments) (auto autoTwin: Option Comments)
    (autos: Option.Alike Anything auto autoTwin) (named namedTwin: List Word)
    (nameds: List.All2 WordsAlike named namedTwin) (atColon: Bool):
    Parse.Follows SameCode GroupsAlike
      (() => headerGroupColon self inner kind refused implicit started open auto named atColon)
      (() => headerGroupColon selfTwin inner kind refused implicit startedTwin openTwin autoTwin namedTwin atColon) :=
  match !atColon with
    | True => followsFatalAny _ (() => Syntax.fatal "a parameter needs a type")
    | False => Parse.followsThen followsFixedFrom (colon colonTwin colons =>
      Parse.followsThen (followsBinderType knot inner) (annotation annotationTwin annotations =>
        followsThenEq
          [j := atEquals =>
            (let default := headerDefault self inner implicit atEquals;
             let close := inner.expectFixed (closerOf implicit) (closeMessage implicit auto named);
             let consumed := consumedBare started;
             headerGroupEnd kind implicit open auto named colon annotation default close refused consumed)]
          [k := atEquals =>
            (let default := headerDefault selfTwin inner implicit atEquals;
             let close := inner.expectFixed (closerOf implicit) (closeMessage implicit autoTwin namedTwin);
             let consumed := consumedBare startedTwin;
             headerGroupEnd kind implicit openTwin autoTwin namedTwin colonTwin annotationTwin default close refused
                 consumed)]
          (followsAt inner ColonEq)
          (atEquals =>
            Parse.followsThen (followsHeaderDefault knot inner implicit atEquals) (default defaultTwin defaults =>
              Parse.followsThen
                (followsExpectFixedTwo inner
                  (closerOf implicit)
                  (closeMessage implicit auto named)
                  (closeMessage implicit autoTwin namedTwin))
                (close closeTwin closes =>
                  Parse.followsThen (followsConsumedBare started startedTwin) (consumed consumedTwin consumeds =>
                    followsHeaderGroupEnd kind implicit open openTwin auto autoTwin autos named namedTwin nameds colon
                        colonTwin annotation annotationTwin annotations default defaultTwin defaults close closeTwin
                        refused consumed consumedTwin))))))

theorem autoSplitAlike ∀ (implicit: Bool) (names namesTwin: List Word)
    (alike: List.All2 WordsAlike names namesTwin):
    PairAlike
      (Option.Alike Anything)
      (List.All2 WordsAlike)
      (autoSplit implicit names)
      (autoSplit implicit namesTwin) :=
  match names, namesTwin with
    | [], [] => (Trivial, Trivial)
    | [word], [twin] => (Trivial, alike)
    | [word, second, ..more], [twin, secondTwin, ..moreTwin] =>
      rewrite wordTextSame word twin alike.left then
        match implicit && twin.text == "auto" with
          | True => (Trivial, alike.right)
          | False => (Trivial, alike)
    | [word], [twin, second, ..more] => alike.right.impossible
    | [word, second, ..more], [twin] => alike.right.impossible

theorem followsHeaderGroupNamed ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (inner: Modes) (kind: GroupKind) (refused: Option Text) (implicit: Bool) (started startedTwin: Parse.Mark Item)
    (open openTwin: Comments) (split splitTwin: (Option Comments, List Word))
    (splits: PairAlike (Option.Alike Anything) (List.All2 WordsAlike) split splitTwin):
    Parse.Follows SameCode GroupsAlike
      (() => headerGroupNamed self inner kind refused implicit started open split)
      (() => headerGroupNamed selfTwin inner kind refused implicit startedTwin openTwin splitTwin) :=
  match split, splitTwin with
    | (auto, named), (autoTwin, namedTwin) =>
      followsThenEq
        [j := atColon => headerGroupColon self inner kind refused implicit started open auto named atColon]
        [k := atColon =>
          headerGroupColon selfTwin inner kind refused implicit startedTwin openTwin autoTwin namedTwin atColon]
        (followsAt inner Colon)
        (atColon =>
          followsHeaderGroupColon knot inner kind refused implicit started startedTwin open openTwin auto autoTwin
              splits.left named namedTwin splits.right atColon)

theorem followsHeaderGroupTyped ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (inner: Modes) (kind: GroupKind) (refused: Option Text) (implicit: Bool) (started startedTwin: Parse.Mark Item)
    (open openTwin: Comments) (names namesTwin: List Word)
    (nameses: List.All2 WordsAlike names namesTwin):
    Parse.Follows SameCode GroupsAlike
      (() => headerGroupTyped self inner kind refused implicit started open names)
      (() => headerGroupTyped selfTwin inner kind refused implicit startedTwin openTwin namesTwin) :=
  followsHeaderGroupNamed knot inner kind refused implicit started startedTwin open openTwin
    (autoSplit implicit names)
    (autoSplit implicit namesTwin)
    (autoSplitAlike implicit names namesTwin nameses)

theorem followsHeaderGroupAuto ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (inner: Modes) (kind: GroupKind) (open openTwin: Comments) (auto autoTwin: Word):
    Parse.Follows SameCode GroupsAlike (() => headerGroupAuto self inner kind open auto) (() =>
      headerGroupAuto selfTwin inner kind openTwin autoTwin) :=
  Parse.followsThen (followsFull knot inner) (annotation annotationTwin annotations =>
    Parse.followsThen
      (followsExpectFixed inner RBracket "`]` to close the parameter `[auto …]`")
      (close closeTwin closes =>
        Parse.followsDone _ _
          (alikeGroup kind True open openTwin [] [] Trivial
            (Some auto.comments)
            (Some autoTwin.comments)
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
            False)))

theorem followsHeaderGroupNames ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (inner: Modes) (kind: GroupKind) (refused: Option Text) (implicit: Bool) (started startedTwin: Parse.Mark Item)
    (open openTwin: Comments) (names namesTwin: List Word)
    (nameses: List.All2 WordsAlike names namesTwin) (typeFollows: Bool):
    Parse.Follows SameCode GroupsAlike
      (() => headerGroupNames self inner kind refused implicit started open names typeFollows)
      (() => headerGroupNames selfTwin inner kind refused implicit startedTwin openTwin namesTwin typeFollows) :=
  match names, namesTwin with
    | [auto], [autoTwin] =>
      let texts: auto.text = autoTwin.text := wordTextSame auto autoTwin nameses.left
      let guards: (implicit && auto.text == "auto" && typeFollows)
        = (implicit && autoTwin.text == "auto" && typeFollows) :=
        Eq.cong (text => implicit && text == "auto" && typeFollows) texts
      match first: implicit && auto.text == "auto" && typeFollows, second: implicit
        && autoTwin.text == "auto"
        && typeFollows with
        | True, True => followsHeaderGroupAuto knot inner kind open openTwin auto autoTwin
        | False, False =>
          followsHeaderGroupTyped knot inner kind refused implicit started startedTwin open openTwin
            [auto]
            [autoTwin]
            nameses
    | [], [] => followsHeaderGroupTyped knot inner kind refused implicit started startedTwin open openTwin [] [] nameses
    | [first, second, ..more], [firstTwin, secondTwin, ..moreTwin] =>
      followsHeaderGroupTyped knot inner kind refused implicit started startedTwin open openTwin
        [first, second, ..more]
        [firstTwin, secondTwin, ..moreTwin]
        nameses
    | [word], [twin, second, ..more] => nameses.right.impossible
    | [word, second, ..more], [twin] => nameses.right.impossible

theorem followsHeaderGroupParts ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (modes: Modes) (kind: GroupKind) (refused: Option Text) (implicit: Bool):
    Parse.Follows SameCode GroupsAlike (() => headerGroupParts self modes kind refused implicit) (() =>
      headerGroupParts selfTwin modes kind refused implicit) :=
  Parse.followsThen Parse.followsMark (started startedTwin marks =>
    Parse.followsThen followsFixedFrom (open openTwin opens =>
      Parse.followsThen (followsAttributesOf modes.inBrackets) (attributes attributesTwin attributeses =>
        Parse.followsThen
          (followsRefuseAttributes attributes attributesTwin attributeses "a definition's parameter")
          (refusal refusalTwin refusals =>
            Parse.followsThen (followsParamName modes.inBrackets) (first firstTwin firsts =>
              Parse.followsThen (followsParamNames modes.inBrackets) (more moreTwin mores =>
                followsThenEq (followsAt modes.inBrackets Colon) (atColon =>
                  followsThenEq (followsAt modes.inBrackets RBracket) (atBracket =>
                    followsThenEq (followsPeek modes.inBrackets) (next =>
                      followsHeaderGroupNames knot modes.inBrackets kind refused implicit started startedTwin open
                          openTwin
                          [first, ..more]
                          [firstTwin, ..moreTwin]
                          (Both firsts mores)
                          (typeFollowsOf atColon atBracket next))))))))))

theorem followsHeaderGroupOn ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (modes: Modes) (kind: GroupKind) (refused: Option Text) (first second: Option Tok):
    Parse.Follows SameCode GroupsAlike (() => headerGroupOn self modes kind refused first second) (() =>
      headerGroupOn selfTwin modes kind refused first second) :=
  match first, second with
    | Some LParen, Some RParen => Parse.followsThen followsFixedFrom (open openTwin opens =>
      Parse.followsThen followsFixedFrom (close closeTwin closes =>
        Parse.followsDone _ _
          (alikeGroup kind False open openTwin [] [] Trivial None None Trivial [] [] Trivial None None Trivial None None
              Trivial None None Trivial close closeTwin False False)))
    | Some LParen, _ => followsHeaderGroupParts knot modes kind refused False
    | Some LBracket, _ => followsHeaderGroupParts knot modes kind refused True
    | _, _ => followsFail modes "a parameter such as `(x: Nat)`, or `:` and the definition's type" (() =>
      modes.fail "a parameter such as `(x: Nat)`, or `:` and the definition's type")

theorem followsHeaderGroupSeen ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (modes: Modes) (kind: GroupKind) (refused: Option Text) (first: Option Tok):
    Parse.Follows SameCode GroupsAlike (() => headerGroupSeen self modes kind refused first) (() =>
      headerGroupSeen selfTwin modes kind refused first) :=
  followsThenEq (followsPeekAt modes 1) (second => followsHeaderGroupOn knot modes kind refused first second)

theorem followsHeaderGroup ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (modes: Modes) (kind: GroupKind) (refused: Option Text):
    Parse.Follows SameCode GroupsAlike (() => headerGroup self modes kind refused) (() =>
      headerGroup selfTwin modes kind refused) :=
  followsPeeked modes
    (first => headerGroupSeen self modes kind refused first)
    (first => headerGroupSeen selfTwin modes kind refused first)
    (first => followsHeaderGroupSeen knot modes kind refused first)

-- Rows and result types.

def RowsAlike (row twin: Row): Prop := (walkRow blankPure row).blank = (walkRow blankPure twin).blank

theorem commentsWordBlank ∀ (found twin: Option (Comments, Word))
    (alike: Option.Alike (PairAlike Anything WordsAlike) found twin):
    blankCommentsWord found = blankCommentsWord twin :=
  match found, twin with
    | Some (c, x), Some (d, y) =>
      let same: x.blank = y.blank := alike.right
      calc blankCommentsWord (Some (c, x))
        _ = Some (Comments.none, x.blank) := byComputing
        _ = Some (Comments.none, y.blank) := rewrite same
        _ = blankCommentsWord (Some (d, y)) := byComputing
    | None, None => byComputing

theorem alikeRow ∀ (open openTwin: Comments) (abilities twins: List Expr)
    (alike: List.All2 ExprsAlike abilities twins) (variable variableTwin: Option (Comments, Word))
    (variables: Option.Alike (PairAlike Anything WordsAlike) variable variableTwin) (close closeTwin: Comments):
    RowsAlike { open, abilities, variable, close } {
      open = openTwin,
      abilities = twins,
      variable = variableTwin,
      close = closeTwin
    } :=
  calc (walkRow blankPure { open, abilities, variable, close }).blank
    _ = {
        open = Comments.none,
        abilities = walkExprs blankPure abilities,
        variable = blankCommentsWord variable,
        close = Comments.none
      } := byComputing
    _ = {
        open = Comments.none,
        abilities = walkExprs blankPure twins,
        variable = blankCommentsWord variableTwin,
        close = Comments.none
      } := rewrite walkExprsAlike abilities twins alike, commentsWordBlank variable variableTwin variables
    _ = (walkRow blankPure { open = openTwin, abilities = twins, variable = variableTwin, close = closeTwin }).blank :=
      byComputing

theorem alikeEffect ∀ (row twin: Row)
    (rows: RowsAlike row twin) (result resultTwin: Expr)
    (results: ExprsAlike result resultTwin):
    ExprsAlike (Effect row result) (Effect twin resultTwin) :=
  calc (Effect row result).walk blankPure
    _ = Effect (walkRow blankPure row).blank (result.walk blankPure) := byComputing
    _ = Effect (walkRow blankPure twin).blank (resultTwin.walk blankPure) := rewrite rows, results
    _ = (Effect twin resultTwin).walk blankPure := byComputing

theorem alikeFunctionType ∀ (binder twin: Group)
    (binders: GroupsAlike binder twin) (arrow arrowTwin: Word)
    (arrows: WordsAlike arrow arrowTwin) (result resultTwin: Expr)
    (results: ExprsAlike result resultTwin):
    ExprsAlike (FunctionType binder arrow result) (FunctionType twin arrowTwin resultTwin) :=
  calc (FunctionType binder arrow result).walk blankPure
    _ = FunctionType (binder.walk blankPure).blank arrow.blank (result.walk blankPure) := byComputing
    _ = FunctionType (twin.walk blankPure).blank arrowTwin.blank (resultTwin.walk blankPure) :=
      rewrite binders, arrows, results
    _ = (FunctionType twin arrowTwin resultTwin).walk blankPure := byComputing

theorem followsRowPart ∀ (modes: Modes) (pipe: Bool):
    Parse.Follows SameCode (Option.Alike (PairAlike Anything WordsAlike)) (() => rowPart modes pipe) (() =>
      rowPart modes pipe) :=
  match pipe with
    | True => Parse.followsThen followsFixedFrom (bar barTwin bars =>
      Parse.followsMap
        (name => Some (bar, name))
        (name => Some (barTwin, name))
        (name nameTwin names => (bars, names))
        (followsLower modes "a row variable"))
    | False => Parse.followsDone None None Trivial

theorem followsRowClose ∀ (modes: Modes) (open openTwin: Comments) (abilities twins: List Expr)
    (alike: List.All2 ExprsAlike abilities twins) (variable variableTwin: Option (Comments, Word))
    (variables: Option.Alike (PairAlike Anything WordsAlike) variable variableTwin):
    Parse.Follows SameCode RowsAlike (() => rowClose modes open abilities variable) (() =>
      rowClose modes openTwin twins variableTwin) :=
  Parse.followsThen (followsExpectFixed modes RBrace "`}`") (close closeTwin closes =>
    Parse.followsDone _ _
      (alikeRow open openTwin abilities twins alike variable variableTwin variables close closeTwin))

theorem followsRowVariable ∀ (modes: Modes) (open openTwin: Comments) (abilities twins: List Expr)
    (alike: List.All2 ExprsAlike abilities twins):
    Parse.Follows SameCode RowsAlike (() => rowVariable modes open abilities) (() =>
      rowVariable modes openTwin twins) :=
  followsThenEq
    [j := pipe => (let variable := rowPart modes pipe; rowClose modes open abilities variable)]
    [k := pipe => (let variable := rowPart modes pipe; rowClose modes openTwin twins variable)]
    (followsAt modes Pipe)
    (pipe =>
      Parse.followsThen (followsRowPart modes pipe) (variable variableTwin variables =>
        followsRowClose modes open openTwin abilities twins alike variable variableTwin variables))

theorem rowEntriesAlike ∀ (pair pairTwin: (List Expr, Bool))
    (pairs: PairAlike (List.All2 ExprsAlike) Same pair pairTwin):
    List.All2 ExprsAlike (rowEntries pair) (rowEntries pairTwin) :=
  match pair, pairTwin with | (entries, closed), (twins, closedTwin) => pairs.left

theorem followsRowAbilities ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (modes: Modes) (closed pipe: Bool):
    Parse.Follows SameCode (List.All2 ExprsAlike) (() => rowAbilities self modes closed pipe) (() =>
      rowAbilities selfTwin modes closed pipe) :=
  match closed || pipe with
    | True => Parse.followsDone [] [] Trivial
    | False => Parse.followsThen (knot { modes, level = LevelApp }) (first firstTwin firsts =>
      Parse.followsThen
        [p := () => Parse.mark()]
        [q := () => Parse.mark()]
        [j := here =>
          rowEntries
            (commaList (here.left + 1) modes (count => False) (() => self { modes, level = LevelApp }) first [])]
        [k := here =>
          rowEntries
            (commaList
              (here.left + 1)
              modes
              (count => False)
              (() => selfTwin { modes, level = LevelApp })
              firstTwin
              [])]
        Parse.followsMark
        (here hereTwin marks =>
          rewrite marks.right.right then
            Parse.followsMap
              (pair => rowEntries pair)
              (pair => rowEntries pair)
              (pair pairTwin pairs => rowEntriesAlike pair pairTwin pairs)
              (followsCommaList modes
                (count => False)
                (count => False)
                (count => Parse.followsDone False False byComputing)
                (() => self { modes, level = LevelApp })
                (() => selfTwin { modes, level = LevelApp })
                (knot { modes, level = LevelApp })
                (hereTwin.left + 1)
                first
                firstTwin
                firsts
                []
                []
                Trivial)))

theorem followsRowStart ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (modes: Modes) (open openTwin: Comments) (lower: Bool) (second: Option Tok):
    Parse.Follows SameCode RowsAlike (() => rowStart self modes open lower second) (() =>
      rowStart selfTwin modes openTwin lower second) :=
  match lower && isSome Colon second with
    | True =>
      followsFatalAny _ (() => Syntax.fatal "a record type can't be written here: `{` in a type starts an ability row")
    | False =>
      followsThenEq
        [j := closed =>
          (let abilities := rowAbilities self modes closed (modes.at Pipe); rowVariable modes open abilities)]
        [k := closed =>
          (let abilities := rowAbilities selfTwin modes closed (modes.at Pipe); rowVariable modes openTwin abilities)]
        (followsAt modes RBrace)
        (closed =>
          followsThenEq
            [j := pipe => (let abilities := rowAbilities self modes closed pipe; rowVariable modes open abilities)]
            [k := pipe =>
              (let abilities := rowAbilities selfTwin modes closed pipe; rowVariable modes openTwin abilities)]
            (followsAt modes Pipe)
            (pipe =>
              Parse.followsThen (followsRowAbilities knot modes closed pipe) (abilities twins alike =>
                followsRowVariable modes open openTwin abilities twins alike)))

theorem followsRowOf ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin) (modes: Modes):
    Parse.Follows SameCode RowsAlike (() => rowOf self modes) (() => rowOf selfTwin modes) :=
  Parse.followsThen (followsExpectFixed modes LBrace "`{`") (open openTwin opens =>
    followsThenEq (followsAt modes Lower) (lower =>
      followsThenEq (followsPeekAt modes 1) (second => followsRowStart knot modes open openTwin lower second)))

theorem followsEffectResult ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin) (allowed: Modes):
    Parse.Follows SameCode ExprsAlike (() => effectResult self allowed) (() => effectResult selfTwin allowed) :=
  Parse.followsThen (followsRowOf knot allowed) (row rowTwin rows =>
    Parse.followsMap
      (result => Effect row result)
      (result => Effect rowTwin result)
      (result resultTwin results => alikeEffect row rowTwin rows result resultTwin results)
      (followsFull knot allowed))

theorem followsResultRow ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (allowed: Modes) (row: Bool):
    Parse.Follows SameCode ExprsAlike (() => resultRow self allowed row) (() => resultRow selfTwin allowed row) :=
  match row with
    | True => followsEffectResult knot allowed
    | False => followsFull knot allowed

theorem followsRowAhead ∀ (allowed: Modes):
    Parse.Follows SameCode Same (() => rowAhead allowed) (() => rowAhead allowed) :=
  followsThenEq (followsAt allowed LBrace) (atBrace => followsLook (rowOn atBrace) (rowOnDeaf atBrace))

theorem followsResultAllowed ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin) (allowed: Modes):
    Parse.Follows SameCode ExprsAlike (() => resultAllowed self allowed) (() => resultAllowed selfTwin allowed) :=
  followsThenEq (followsRowAhead allowed) (row => followsResultRow knot allowed row)

theorem followsResultType ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin) (modes: Modes):
    Parse.Follows SameCode ExprsAlike (() => resultType self modes) (() => resultType selfTwin modes) :=
  followsThenEq (followsAllowBrace modes) (allowed => followsResultAllowed knot allowed)

-- Binders.

theorem walkAttributesEmpty ∀ (attributes: List Attributes):
    (walkAttributes blankPure attributes).isEmpty = attributes.isEmpty :=
  match attributes with | [] | [_, .._] => byComputing

theorem followsRefuseEmpty ∀ (attributes twins: List Attributes)
    (empties: attributes.isEmpty = twins.isEmpty) (what: Text):
    Parse.Follows SameCode Anything (() => refuseAttributes attributes what) (() => refuseAttributes twins what) :=
  match attributes, twins with
    | [], [] => Parse.followsDone () () Trivial
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
  match atColonEq with
    | True => Parse.followsThen followsFixedFrom (colonEq colonEqTwin colonEqs =>
      Parse.followsMap
        (value => Some (colonEq, value))
        (value => Some (colonEqTwin, value))
        (value valueTwin values => (colonEqs, values))
        (followsFull knot inner))
    | False => Parse.followsDone None None Trivial

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
              followsThenEq
                [alike := GroupsAlike]
                [j := atEquals =>
                  (let default := binderDefault self modes.inBrackets atEquals;
                   let close := modes.inBrackets.expectFixed RParen "`)`";
                   if !defaults && default.isSome then Syntax.fatal defaultPlaces
                   else
                     {
                       kind = GroupBinder,
                       implicit = False,
                       open,
                       attributes,
                       auto = None,
                       names = [first, ..more],
                       colon = Some colon,
                       annotation = Some annotation,
                       default,
                       close,
                       bare = False
                     })]
                [k := atEquals =>
                  (let default := binderDefault selfTwin modes.inBrackets atEquals;
                   let close := modes.inBrackets.expectFixed RParen "`)`";
                   if !defaults && default.isSome then Syntax.fatal defaultPlaces
                   else
                     {
                       kind = GroupBinder,
                       implicit = False,
                       open = openTwin,
                       attributes = attributesTwin,
                       auto = None,
                       names = [firstTwin, ..moreTwin],
                       colon = Some colonTwin,
                       annotation = Some annotationTwin,
                       default,
                       close,
                       bare = False
                     })]
                (followsAt modes.inBrackets ColonEq)
                (atEquals =>
                  Parse.followsThen
                    (followsBinderDefault knot modes.inBrackets atEquals)
                    (default defaultTwin defaults2 =>
                      Parse.followsThen (followsExpectFixed modes.inBrackets RParen "`)`") (close closeTwin closes =>
                        let same: default.isSome = defaultTwin.isSome := optionIsSome default defaultTwin defaults2
                        rewrite same then
                          match !defaults && defaultTwin.isSome with
                            | True => followsFatalAny _ _
                            | False =>
                              Parse.followsDone _ _
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
            Parse.followsDone _ _
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
            Parse.followsDone _ _
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
            (result resultTwin results =>
              alikeFunctionType binder binderTwin binders arrow arrowTwin arrows result resultTwin results)
            (followsResultType knot modes))))

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
  followsThenEq (followsPeek modes) (seen => Parse.followsDone (defKindOn seen) (defKindOn seen) byComputing)

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
  match paren || bracket with
    | True => Parse.followsDone (Some word) (Some twin) words
    | False => followsFail modes "a parameter such as `(x: Nat)` after `∀`" (() =>
      modes.fail "a parameter such as `(x: Nat)` after `∀`")

theorem followsForallBump ∀ (modes: Modes):
    Parse.Follows SameCode (Option.Alike WordsAlike) (() => forallBump modes) (() => forallBump modes) :=
  Parse.followsThen followsBump (theWord twin words =>
    followsThenEq (followsAt modes LParen) (paren =>
      followsThenEq (followsAt modes LBracket) (bracket => followsForallEnd modes theWord twin words paren bracket)))

theorem followsForallAt ∀ (modes: Modes) (kind: DefKind) (found: Bool):
    Parse.Follows SameCode (Option.Alike WordsAlike) (() => forallAt modes kind found) (() =>
      forallAt modes kind found) :=
  match found with
    | True =>
      match kind != DefTheorem with
        | True => followsFatalAny _ (() => Syntax.fatal "`∀` before the parameters is only for theorems")
        | False => followsForallBump modes
    | False => Parse.followsDone None None Trivial

theorem followsForallPart ∀ (modes: Modes) (kind: DefKind):
    Parse.Follows SameCode (Option.Alike WordsAlike) (() => forallPart modes kind) (() => forallPart modes kind) :=
  followsThenEq (followsAt modes KwForall) (found => followsForallAt modes kind found)

theorem followsHeaderParamStep ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (modes: Modes) (atColon: Bool):
    Parse.Follows SameCode (Option.Alike GroupsAlike) (() => headerParamStep self modes atColon) (() =>
      headerParamStep selfTwin modes atColon) :=
  match !atColon with
    | True =>
      Parse.followsMap
        [alike := Option.Alike GroupsAlike]
        [p := () => headerGroup self modes GroupParam None]
        [q := () => headerGroup selfTwin modes GroupParam None]
        (group => Some group)
        (group => Some group)
        (x y alike => alike)
        (followsHeaderGroup knot modes GroupParam None)
    | False => Parse.followsDone None None Trivial

theorem followsHeaderParams ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin) (modes: Modes):
    Parse.Follows SameCode (List.All2 GroupsAlike) (() => headerParams self modes) (() =>
      headerParams selfTwin modes) :=
  Parse.followsLoop _ _ (followsThenEq (followsAt modes Colon) (atColon => followsHeaderParamStep knot modes atColon))

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
  Parse.followsThen followsFixedFrom (keyword keywordTwin keywords =>
    Parse.followsMap
      (tail => Some (keyword, tail))
      (tail => Some (keywordTwin, tail))
      (tail tailTwin tails => (keywords, tails))
      (knot { modes = headerModes, level = LevelFull }))

theorem followsDecreasingAt ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (headerModes: Modes) (isInstance found: Bool):
    Parse.Follows SameCode
      (Option.Alike (PairAlike Anything ExprsAlike))
      (() => decreasingAt self headerModes isInstance found)
      (() => decreasingAt selfTwin headerModes isInstance found) :=
  match found with
    | True =>
      match isInstance with
        | True => followsFatalAny _ _
        | False => followsDecreasingClauseOf knot headerModes
    | False => Parse.followsDone None None Trivial

theorem followsDecreasingPart ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (modes headerModes: Modes) (isInstance: Bool):
    Parse.Follows SameCode
      (Option.Alike (PairAlike Anything ExprsAlike))
      (() => decreasingPart self modes headerModes isInstance)
      (() => decreasingPart selfTwin modes headerModes isInstance) :=
  followsThenEq (followsAt modes KwDecreasing) (found => followsDecreasingAt knot headerModes isInstance found)

theorem followsAfterDecreasingOf ∀ (modes: Modes) (clause clauseTwin: Option (Comments, Expr))
    (clauses: Option.Alike (PairAlike Anything ExprsAlike) clause clauseTwin):
    Parse.Follows SameCode Same (() => afterDecreasingOf modes clause) (() => afterDecreasingOf modes clauseTwin) :=
  let same: clause.isSome = clauseTwin.isSome := optionIsSome clause clauseTwin clauses
  rewrite same then
    match clauseTwin.isSome with
      | True => followsAllowColonEq modes
      | False => Parse.followsDone modes modes byComputing

def UnfoldingNamesFollow (modes: Modes) (fuel: Nat): Prop :=
  ∀ (found twin: List Word) => List.All2 WordsAlike found twin
    → Parse.Follows SameCode (List.All2 WordsAlike) (() => unfoldingNames fuel modes found) (() =>
      unfoldingNames fuel modes twin)

theorem followsUnfoldingName ∀ (modes: Modes) (upper: Bool):
    Parse.Follows SameCode WordsAlike (() => unfoldingName modes upper) (() => unfoldingName modes upper) :=
  match upper with
    | True => followsUpperQualified modes "the name of an opaque definition"
    | False => followsLowerQualified modes "the name of an opaque definition"

theorem followsUnfoldingNext ∀ (more: Nat) (modes: Modes)
    (again: UnfoldingNamesFollow modes more) (found twins: List Word)
    (founds: List.All2 WordsAlike found twins) (name nameTwin: Word)
    (names: WordsAlike name nameTwin) (comma: Bool):
    Parse.Follows SameCode (List.All2 WordsAlike) (() => unfoldingNext more modes found name comma) (() =>
      unfoldingNext more modes twins nameTwin comma) :=
  match comma with
    | True => Parse.followsThen followsBump (skippedItems skippedTwin skips =>
      again [name, ..found] [nameTwin, ..twins] (Both names founds))
    | False => Parse.followsDone _ _ (List.all2Reverse [name, ..found] [nameTwin, ..twins] (Both names founds))

theorem followsUnfoldingNames ∀ (fuel: Nat) (modes: Modes) (found twins: List Word)
    (founds: List.All2 WordsAlike found twins):
    Parse.Follows SameCode (List.All2 WordsAlike) (() => unfoldingNames fuel modes found) (() =>
      unfoldingNames fuel modes twins) :=
  match fuel with
    | Succ more =>
      followsThenEq
        [j := upper => (let name := unfoldingName modes upper; unfoldingNext more modes found name (modes.at Comma))]
        [k := upper => (let name := unfoldingName modes upper; unfoldingNext more modes twins name (modes.at Comma))]
        (followsAt modes Upper)
        (upper =>
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
    | Zero => Parse.followsDone _ _ (List.all2Reverse found twins founds)

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
          (names namesTwin nameses => (keywords, nameses))
          (followsUnfoldingNames fuel afterDecreasing [] [] Trivial)))

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
    | False => Parse.followsDone None None Trivial

theorem followsUnfoldingPart ∀ (modes afterDecreasing: Modes) (isInstance: Bool):
    Parse.Follows SameCode
      (Option.Alike (PairAlike Anything (List.All2 WordsAlike)))
      (() => unfoldingPart modes afterDecreasing isInstance)
      (() => unfoldingPart modes afterDecreasing isInstance) :=
  followsThenEq (followsAt afterDecreasing KwUnfolding) (found => followsUnfoldingAt afterDecreasing isInstance found)

theorem followsAfterUnfoldingOf ∀ (afterDecreasing: Modes) (clause clauseTwin: Option (Comments, List Word))
    (clauses: Option.Alike (PairAlike Anything (List.All2 WordsAlike)) clause clauseTwin):
    Parse.Follows SameCode Same (() => afterUnfoldingOf afterDecreasing clause) (() =>
      afterUnfoldingOf afterDecreasing clauseTwin) :=
  let same: clause.isSome = clauseTwin.isSome := optionIsSome clause clauseTwin clauses
  rewrite same then
    match clauseTwin.isSome with
      | True => followsAllowColonEq afterDecreasing
      | False => Parse.followsDone afterDecreasing afterDecreasing byComputing

theorem followsClauseConflict ∀ (afterUnfolding: Modes) (clause clauseTwin: Option (Comments, List Word))
    (clauses: Option.Alike (PairAlike Anything (List.All2 WordsAlike)) clause clauseTwin):
    Parse.Follows SameCode Same (() => clauseConflict afterUnfolding clause) (() =>
      clauseConflict afterUnfolding clauseTwin) :=
  let same: clause.isSome = clauseTwin.isSome := optionIsSome clause clauseTwin clauses
  followsThenEq (followsAt afterUnfolding KwDecreasing) (found =>
    let conflict: conflictOn found clause = conflictOn found clauseTwin := Eq.cong (some => found && some) same
    Parse.followsDone (conflictOn found clause) (conflictOn found clauseTwin) conflict)

theorem followsBodyModesOf ∀ (afterUnfolding: Modes) (isInstance: Bool) (local: Option Nat):
    Parse.Follows SameCode Same (() => bodyModesOf afterUnfolding isInstance local) (() =>
      bodyModesOf afterUnfolding isInstance local) :=
  match local with
    | Some _ => Parse.followsDone afterUnfolding afterUnfolding byComputing
    | None => followsThenEq (followsAtEither afterUnfolding ColonEq Pipe) (recovering =>
      Parse.followsDone
        (recoverMode afterUnfolding isInstance recovering)
        (recoverMode afterUnfolding isInstance recovering)
        byComputing)

-- Definition bodies.

theorem followsAssignedEnd ∀ (colonEq colonEqTwin: Comments) (value valueTwin: Expr)
    (values: ExprsAlike value valueTwin) (arms: Bool):
    Parse.Follows SameCode DefBodyAlike (() => assignedEnd colonEq value arms) (() =>
      assignedEnd colonEqTwin valueTwin arms) :=
  match arms with
    | True => followsFatalAny _ _
    | False => Parse.followsDone _ _ (alikeAssigned colonEq colonEqTwin value valueTwin values)

theorem followsAssignedValue ∀ (modes: Modes) (colonEq colonEqTwin: Comments) (value valueTwin: Expr)
    (values: ExprsAlike value valueTwin):
    Parse.Follows SameCode DefBodyAlike (() => assignedValue modes colonEq value) (() =>
      assignedValue modes colonEqTwin valueTwin) :=
  followsThenEq (followsAt modes Pipe) (arms => followsAssignedEnd colonEq colonEqTwin value valueTwin values arms)

theorem followsAssignedBody ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin) (modes: Modes):
    Parse.Follows SameCode DefBodyAlike (() => assignedBody self modes) (() => assignedBody selfTwin modes) :=
  Parse.followsThen followsFixedFrom (colonEq colonEqTwin colonEqs =>
    Parse.followsThen (knot { modes, level = LevelFull }) (value valueTwin values =>
      followsAssignedValue modes colonEq colonEqTwin value valueTwin values))

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
      | None => Parse.followsDone body twin bodies

theorem followsDefinitionChecked ∀ (isInstance: Bool) (body twin: DefBody)
    (bodies: DefBodyAlike body twin):
    Parse.Follows SameCode DefBodyAlike (() => definitionChecked isInstance body) (() =>
      definitionChecked isInstance twin) :=
  followsOn
    (items => definitionWhere isInstance body items)
    (items => definitionWhere isInstance twin items)
    (itemList others same => followsDefinitionWhere isInstance body twin bodies itemList others same)

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
            [alike := ArmAlike]
            (body => { bar, patterns, guard, body })
            (body => { bar = barTwin, patterns = patternsTwin, guard = guardTwin, body })
            (body bodyTwin bodies =>
              alikeArm bar barTwin bars patterns patternsTwin patternses guard guardTwin guards body bodyTwin bodies)
            (followsArmBody knot modes (anyAbsurd patternsTwin) "`=>` and the arm's body"))))

theorem followsDefinitionArmStep ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (alts: AltPatternFollows) (modes: Modes) (d column: Nat) (items others: List Item)
    (same: List.All2 SameCode items others):
    Parse.Follows SameCode (Option.Alike ArmAlike) (() => definitionArmStep self modes d column items) (() =>
      definitionArmStep selfTwin modes d column others) :=
  match items, others with
    | [], [] => Parse.followsDone None None Trivial
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
            | True, True => Parse.followsDone None None Trivial
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
                        (arm armTwin arms => arms)
                        (followsDefinitionArm knot alts { modes | allow = Some here }))
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
  Parse.followsLoop _ _
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
  followsOn
    (items => definitionArmsOn self modes d items)
    (items => definitionArmsOn selfTwin modes d items)
    (itemList others same => followsDefinitionArmsOn knot alts modes d itemList others same)

theorem followsArmsBody ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (alts: AltPatternFollows) (modes: Modes) (d: Nat):
    Parse.Follows SameCode DefBodyAlike (() => armsBody self modes d) (() => armsBody selfTwin modes d) :=
  Parse.followsMap
    (arms => Arms arms)
    (arms => Arms arms)
    (arms armsTwin alike => alikeArms arms armsTwin alike)
    (followsDefinitionArms knot alts modes d)

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
          | False => Parse.followsDone Primitive Primitive alikePrimitive

theorem followsDefinitionBody ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (alts: AltPatternFollows) (modes: Modes) (result resultTwin: Expr)
    (results: ExprsAlike result resultTwin)
    (isInstance: Bool) (d: Nat):
    Parse.Follows SameCode DefBodyAlike (() => definitionBody self modes result isInstance d) (() =>
      definitionBody selfTwin modes resultTwin isInstance d) :=
  followsThenEq
    [j := seen => definitionChecked isInstance (definitionBodyOn self modes result d seen)]
    [k := seen => definitionChecked isInstance (definitionBodyOn selfTwin modes resultTwin d seen)]
    (followsPeek modes)
    (seen =>
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
                                            [alike := PairAlike HeaderAlike DefBodyAlike]
                                            [p := () =>
                                              definitionBody self afterUnfolding result
                                                (kind == DefInstance)
                                                (local.getOrElse 0)]
                                            [q := () =>
                                              definitionBody selfTwin afterUnfolding resultTwin
                                                (kind == DefInstance)
                                                (local.getOrElse 0)]
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
                                            (body bodyTwin bodies =>
                                              (
                                                alikeHeader exportKeyword exportTwin opaqueKeyword opaqueTwin exports
                                                    opaques kind keyword keywordTwin name nameTwin names forallKeyword
                                                    forallTwin foralls params paramsTwin paramses colon colonTwin result
                                                    resultTwin results clause clauseTwin clauses opacity opacityTwin
                                                    opacities,
                                                bodies
                                              ))
                                            (followsDefinitionBody knot alts afterUnfolding result resultTwin results
                                              (kind == DefInstance)
                                              (local.getOrElse 0)))))))))))))))
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
                                              (body bodyTwin bodies =>
                                                (
                                                  alikeHeader exportKeyword exportTwin opaqueKeyword opaqueTwin exports
                                                      opaques kind keyword keywordTwin name nameTwin names forallKeyword
                                                      forallTwin foralls params paramsTwin paramses colon colonTwin
                                                      result resultTwin results clause clauseTwin clauses opacity
                                                      opacityTwin opacities,
                                                  bodies
                                                ))
                                              (followsDefinitionBody knot alts bodyModes result resultTwin results
                                                (kind == DefInstance)
                                                (local.getOrElse 0)))))))))))))))

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
  match items, twins with
    | [], [] => byComputing
    | [item, ..rest], [twin, ..restTwin] =>
      let (head, tail) := alike
      calc blankImportItems [item, ..rest]
        _ = [importItemKey item, ..blankImportItems rest] := importItemsCons item rest
        _ = [importItemKey twin, ..blankImportItems restTwin] := rewrite head, importItemsBlank rest restTwin tail
        _ = blankImportItems [twin, ..restTwin] := Eq.flipped (importItemsCons twin restTwin)

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
  match items, twins with
    | [], [] => byComputing
    | [item, ..rest], [twin, ..restTwin] =>
      let (head, tail) := alike
      calc blankOperations (walkOperations blankPure [item, ..rest])
        _ = [operationKey item, ..blankOperations (walkOperations blankPure rest)] := operationsCons item rest
        _ = [operationKey twin, ..blankOperations (walkOperations blankPure restTwin)] :=
          rewrite head, operationsBlank rest restTwin tail
        _ = blankOperations (walkOperations blankPure [twin, ..restTwin]) := Eq.flipped (operationsCons twin restTwin)

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
  match steps, twins with
    | [], [] => byComputing
    | [step, ..rest], [twin, ..restTwin] =>
      let (head, tail) := alike
      calc blankIndexSteps (walkIndices blankPure [step, ..rest])
        _ = [stepKey step, ..blankIndexSteps (walkIndices blankPure rest)] := blankIndexStepsCons step rest
        _ = [stepKey twin, ..blankIndexSteps (walkIndices blankPure restTwin)] :=
          rewrite head, indexStepsBlank rest restTwin tail
        _ = blankIndexSteps (walkIndices blankPure [twin, ..restTwin]) := Eq.flipped (blankIndexStepsCons twin restTwin)

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
  match fields, twins with
    | [], [] => byComputing
    | [field, ..rest], [twin, ..restTwin] =>
      let (head, tail) := alike
      calc blankFieldList (walkFieldList blankPure [field, ..rest])
        _ = [fieldKey field, ..blankFieldList (walkFieldList blankPure rest)] := fieldsCons field rest
        _ = [fieldKey twin, ..blankFieldList (walkFieldList blankPure restTwin)] :=
          rewrite head, fieldListBlank rest restTwin tail
        _ = blankFieldList (walkFieldList blankPure [twin, ..restTwin]) := Eq.flipped (fieldsCons twin restTwin)

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
  match parts, twins with
    | [], [] => byComputing
    | [part, ..rest], [twin, ..restTwin] =>
      let (head, tail) := alike
      calc blankParts (walkParts blankPure [part, ..rest])
        _ = [partKey part, ..blankParts (walkParts blankPure rest)] := partsCons part rest
        _ = [partKey twin, ..blankParts (walkParts blankPure restTwin)] := rewrite head, partsBlank rest restTwin tail
        _ = blankParts (walkParts blankPure [twin, ..restTwin]) := Eq.flipped (partsCons twin restTwin)

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
  match items, twins with
    | [], [] => byComputing
    | [item, ..rest], [twin, ..restTwin] =>
      let (head, tail) := alike
      calc blankConstructors (walkConstructors blankPure [item, ..rest])
        _ = [constructorKey item, ..blankConstructors (walkConstructors blankPure rest)] := constructorsCons item rest
        _ = [constructorKey twin, ..blankConstructors (walkConstructors blankPure restTwin)] :=
          rewrite head, constructorsBlank rest restTwin tail
        _ = blankConstructors (walkConstructors blankPure [twin, ..restTwin]) :=
          Eq.flipped (constructorsCons twin restTwin)

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
  match indices, body with
    | None, Abstract | Synonym _ _ | RecordBody _ _ | Sum _ _ => byComputing
    | Some { colon, steps, last }, Abstract => byComputing
    | Some { colon, steps, last }, Synonym equals annotation => byComputing
    | Some { colon, steps, last }, RecordBody equals fields => byComputing
    | Some { colon, steps, last }, Sum equals constructors => byComputing

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
        (name nameTwin names => alikeNamespace keyword keywordTwin name nameTwin names)
        followsBump
    | Some Lower => followsFatalAny _ _
    | _ => followsFail modes "a namespace, such as `Day05`" (() => modes.fail "a namespace, such as `Day05`")

theorem followsNamespaceLine ∀ (modes: Modes):
    Parse.Follows SameCode DeclsAlike (() => namespaceLine modes) (() => namespaceLine modes) :=
  Parse.followsThen followsFixedFrom (keyword keywordTwin keywords =>
    followsThenEq (followsPeek modes) (seen => followsNamespaceAfter modes keyword keywordTwin seen))

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
                  [alike := Option.Alike (PairAlike Anything WordsAlike)]
                  [p := () => bump()]
                  [q := () => bump()]
                  (word => Some (asWord, word))
                  (word => Some (asWordTwin, word))
                  (theWord wordTwin words => (Trivial, words))
                  followsBump
        | False, False => followsFail modes "the name to use instead, as in `x as y`" (() =>
          modes.fail "the name to use instead, as in `x as y`")
    | [], [] => followsFail modes "the name to use instead, as in `x as y`" (() =>
      modes.fail "the name to use instead, as in `x as y`")

theorem followsImportAliasOn ∀ (modes: Modes) (name nameTwin: Word)
    (names: WordsAlike name nameTwin) (asNext: Bool):
    Parse.Follows SameCode (Option.Alike (PairAlike Anything WordsAlike)) (() => importAliasOn modes name asNext) (() =>
      importAliasOn modes nameTwin asNext) :=
  match asNext with
    | True => Parse.followsThen followsFixedFrom (asWord asWordTwin asWords =>
      followsOn
        (items => importAliasWord modes name asWord items)
        (items => importAliasWord modes nameTwin asWordTwin items)
        (itemList others same =>
          followsImportAliasWord modes name nameTwin names asWord asWordTwin itemList others same))
    | False => Parse.followsDone None None Trivial

theorem followsImportAlias ∀ (modes: Modes) (name nameTwin: Word)
    (names: WordsAlike name nameTwin):
    Parse.Follows SameCode (Option.Alike (PairAlike Anything WordsAlike)) (() => importAlias modes name) (() =>
      importAlias modes nameTwin) :=
  followsThenEq (followsWordAhead modes "as") (asNext => followsImportAliasOn modes name nameTwin names asNext)

def ImportItemsFollow (modes: Modes) (path pathTwin: Word) (fuel: Nat): Prop :=
  ∀ (found twins: List ImportItem) => List.All2 ImportItemAlike found twins
    → Parse.Follows SameCode (List.All2 ImportItemAlike) (() => importItems fuel modes path found) (() =>
      importItems fuel modes pathTwin twins)

theorem followsImportTail ∀ (more: Nat) (modes: Modes) (path pathTwin: Word)
    (again: ImportItemsFollow modes path pathTwin more) (done twins: List ImportItem)
    (dones: List.All2 ImportItemAlike done twins) (comma: Bool):
    Parse.Follows SameCode (List.All2 ImportItemAlike) (() => importTail more modes path done comma) (() =>
      importTail more modes pathTwin twins comma) :=
  match comma with
    | True => Parse.followsThen followsBump (skippedItems skippedTwin skips => again done twins dones)
    | False => Parse.followsDone _ _ (List.all2Reverse done twins dones)

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
  followsThenEq (followsAt modes DotDot) (dots => followsImportStop modes path pathTwin found twins founds dots)

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
        (itemList twins alike => alikeImportItems itemList twins alike)
        (followsImportItems fuel modes path pathTwin [] [] Trivial))

theorem followsImportAllEnd ∀ (path pathTwin: Word) (dots dotsTwin: Comments) (closed: Bool):
    Parse.Follows SameCode ImportedAlike (() => importAllEnd path dots closed) (() =>
      importAllEnd pathTwin dotsTwin closed) :=
  match closed with
    | True => Parse.followsDone _ _ (alikeImportAll dots dotsTwin)
    | False => followsFatalAny _ (() => Syntax.fatal (mixedImport pathTwin))

theorem followsImportedOf ∀ (modes: Modes) (path pathTwin: Word) (dots: Bool):
    Parse.Follows SameCode ImportedAlike (() => importedOf modes path dots) (() => importedOf modes pathTwin dots) :=
  match dots with
    | True => Parse.followsThen followsFixedFrom (written writtenTwin writtens =>
      followsThenEq (followsAt modes RParen) (closed => followsImportAllEnd path pathTwin written writtenTwin closed))
    | False => followsImportNames modes path pathTwin

theorem followsImportClose ∀ (modes: Modes) (keyword keywordTwin: Comments) (path pathTwin: Word)
    (paths: WordsAlike path pathTwin)
    (open openTwin: Comments) (imported importedTwin: Imported)
    (importeds: ImportedAlike imported importedTwin):
    Parse.Follows SameCode DeclsAlike (() => importClose modes keyword path open imported) (() =>
      importClose modes keywordTwin pathTwin openTwin importedTwin) :=
  Parse.followsThen (followsExpectFixed modes RParen "`)`") (close closeTwin closes =>
    Parse.followsDone _ _
      (alikeImport keyword keywordTwin path pathTwin paths open openTwin imported importedTwin importeds close
          closeTwin))

theorem followsImportOpen ∀ (modes: Modes) (keyword keywordTwin: Comments) (path pathTwin: Word)
    (paths: WordsAlike path pathTwin):
    Parse.Follows SameCode DeclsAlike (() => importOpen modes keyword path) (() =>
      importOpen modes keywordTwin pathTwin) :=
  Parse.followsThen (followsExpectFixed modes LParen "`(` and the names to import") (open openTwin opens =>
    followsThenEq
      [j := dots => (let imported := importedOf modes path dots; importClose modes keyword path open imported)]
      [k := dots =>
        (let imported := importedOf modes pathTwin dots; importClose modes keywordTwin pathTwin openTwin imported)]
      (followsAt modes DotDot)
      (dots =>
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
  match upper with
    | True => followsBump
    | False => followsFail modes "a namespace, such as `List`" (() => modes.fail "a namespace, such as `List`")

theorem followsImportLine ∀ (modes: Modes):
    Parse.Follows SameCode DeclsAlike (() => importLine modes) (() => importLine modes) :=
  Parse.followsThen followsFixedFrom (keyword keywordTwin keywords =>
    followsThenEq
      [j := upper => (let path := importPath modes upper; importAfter modes keyword path (wordAhead modes "as"))]
      [k := upper => (let path := importPath modes upper; importAfter modes keywordTwin path (wordAhead modes "as"))]
      (followsAt modes Upper)
      (upper =>
        Parse.followsThen (followsImportPath modes upper) (path pathTwin paths =>
          followsThenEq (followsWordAhead modes "as") (asNext =>
            followsImportAfter modes keyword keywordTwin path pathTwin paths asNext))))

-- Fields and constructors of data declarations.

def ExpressionRule: Prop :=
  ∀ (self selfTwin: Goal → {Parse Item} Expr) => SelfFollows self selfTwin
    → SelfFollows (expressionRule self) (expressionRule selfTwin)

theorem expressionKnot ∀ (rule: ExpressionRule): SelfFollows expressionAt expressionAt := goal =>
  followsExpressionAt rule goal

theorem fieldListEmpty ∀ (fields: List Field):
    (blankFieldList (walkFieldList blankPure fields)).isEmpty = fields.isEmpty :=
  match fields with | [] | [_, .._] => byComputing

theorem fieldsWalkFields ∀ (fields: Fields):
    (fields.walk blankPure).fields = blankFieldList (walkFieldList blankPure fields.fields) :=
  match fields with | { open, fields, trailingComma, close } => byComputing

theorem fieldsEmpty ∀ (fields twin: Fields)
    (alike: FieldsAlike fields twin):
    fields.fields.isEmpty = twin.fields.isEmpty :=
  let same: blankFieldList (walkFieldList blankPure fields.fields)
    = blankFieldList (walkFieldList blankPure twin.fields) :=
    calc blankFieldList (walkFieldList blankPure fields.fields)
      _ = (fields.walk blankPure).fields := Eq.flipped (fieldsWalkFields fields)
      _ = (twin.walk blankPure).fields := Eq.cong (found => found.fields) alike
      _ = blankFieldList (walkFieldList blankPure twin.fields) := fieldsWalkFields twin
  calc fields.fields.isEmpty
    _ = (blankFieldList (walkFieldList blankPure fields.fields)).isEmpty := Eq.flipped (fieldListEmpty fields.fields)
    _ = (blankFieldList (walkFieldList blankPure twin.fields)).isEmpty := rewrite same
    _ = twin.fields.isEmpty := fieldListEmpty twin.fields

theorem followsFieldDefault ∀ (rule: ExpressionRule) (modes: Modes) (atColonEq: Bool):
    Parse.Follows SameCode (Option.Alike (PairAlike Anything ExprsAlike)) (() => fieldDefault modes atColonEq) (() =>
      fieldDefault modes atColonEq) :=
  match atColonEq with
    | True => Parse.followsThen followsFixedFrom (colonEq colonEqTwin colonEqs =>
      Parse.followsMap
        (value => Some (colonEq, value))
        (value => Some (colonEqTwin, value))
        (value valueTwin values => (colonEqs, values))
        (followsExpressionAt rule { modes, level = LevelFull }))
    | False => Parse.followsDone None None Trivial

def FieldsFromFollow (modes: Modes) (fuel: Nat): Prop :=
  ∀ (found twins: List Field) => List.All2 FieldAlike found twins
    → Parse.Follows SameCode (PairAlike (List.All2 FieldAlike) Same) (() => fieldsFrom fuel modes found) (() =>
      fieldsFrom fuel modes twins)

theorem followsFieldsNext ∀ (more: Nat) (modes: Modes)
    (again: FieldsFromFollow modes more) (done twins: List Field)
    (dones: List.All2 FieldAlike done twins) (comma: Bool):
    Parse.Follows SameCode (PairAlike (List.All2 FieldAlike) Same) (() => fieldsNext more modes done comma) (() =>
      fieldsNext more modes twins comma) :=
  match comma with
    | True => Parse.followsThen followsBump (skippedItems skippedTwin skips => again done twins dones)
    | False => Parse.followsDone _ _ (List.all2Reverse done twins dones, byComputing)

theorem followsFieldsAt ∀ (rule: ExpressionRule) (more: Nat) (modes: Modes)
    (again: FieldsFromFollow modes more) (found twins: List Field)
    (founds: List.All2 FieldAlike found twins) (closed: Bool):
    Parse.Follows SameCode (PairAlike (List.All2 FieldAlike) Same) (() => fieldsAt more modes found closed) (() =>
      fieldsAt more modes twins closed) :=
  match closed with
    | True => Parse.followsDone _ _ (List.all2Reverse found twins founds, byComputing)
    | False => Parse.followsThen (followsAttributesOf modes) (attributes attributesTwin attributeses =>
      Parse.followsThen (followsLower modes "a field name") (name nameTwin names =>
        Parse.followsThen (followsExpectFixed modes Colon "`:`") (colon colonTwin colons =>
          Parse.followsThen
            (followsExpressionAt rule { modes, level = LevelFull })
            (annotation annotationTwin annotations =>
              followsThenEq
                [j := atEquals =>
                  (let default := fieldDefault modes atEquals;
                   let done := [{ attributes, name, colon, annotation, default }, ..found];
                   fieldsNext more modes done (modes.at Comma))]
                [k := atEquals =>
                  (let default := fieldDefault modes atEquals;
                   let done := [
                     {
                       attributes = attributesTwin,
                       name = nameTwin,
                       colon = colonTwin,
                       annotation = annotationTwin,
                       default
                     },
                     ..twins
                   ];
                   fieldsNext more modes done (modes.at Comma))]
                (followsAt modes ColonEq)
                (atEquals =>
                  Parse.followsThen (followsFieldDefault rule modes atEquals) (default defaultTwin defaults =>
                    followsThenEq (followsAt modes Comma) (comma =>
                      followsFieldsNext more modes again
                        [{ attributes, name, colon, annotation, default }, ..found]
                        [
                          {
                            attributes = attributesTwin,
                            name = nameTwin,
                            colon = colonTwin,
                            annotation = annotationTwin,
                            default = defaultTwin
                          },
                          ..twins
                        ]
                        (Both
                          (alikeField attributes attributesTwin attributeses name nameTwin names colon colonTwin
                              annotation annotationTwin annotations default defaultTwin defaults)
                          founds)
                        comma)))))))

theorem followsFieldsFrom ∀ (rule: ExpressionRule) (fuel: Nat) (modes: Modes) (found twins: List Field)
    (founds: List.All2 FieldAlike found twins):
    Parse.Follows SameCode (PairAlike (List.All2 FieldAlike) Same) (() => fieldsFrom fuel modes found) (() =>
      fieldsFrom fuel modes twins) :=
  match fuel with
    | Succ more => followsThenEq (followsAt modes RBrace) (closed =>
      followsFieldsAt rule more modes
        (again twinsAgain agains => followsFieldsFrom rule more modes again twinsAgain agains)
        found
        twins
        founds
        closed)
    | Zero => Parse.followsDone _ _ (List.all2Reverse found twins founds, byComputing)

theorem followsBracedFieldsIn ∀ (rule: ExpressionRule) (inner: Modes) (closed: Bool):
    Parse.Follows SameCode (PairAlike (List.All2 FieldAlike) Same) (() => bracedFieldsIn inner closed) (() =>
      bracedFieldsIn inner closed) :=
  match closed with
    | True => Parse.followsDone ([], False) ([], False) (Trivial, byComputing)
    | False => followsFuel (fuel => fieldsFrom fuel inner []) (fuel => fieldsFrom fuel inner []) (fuel =>
      followsFieldsFrom rule fuel inner [] [] Trivial)

theorem followsBracedFields ∀ (rule: ExpressionRule) (modes: Modes):
    Parse.Follows SameCode FieldsAlike (() => bracedFields modes) (() => bracedFields modes) :=
  Parse.followsThen (followsExpectFixed modes LBrace "`{`") (open openTwin opens =>
    followsThenEq
      [j := closed =>
        (let (fields, trailingComma) := bracedFieldsIn modes.inBrackets closed;
         let close := modes.inBrackets.expectFixed RBrace "`,` or `}`";
         ({ open, fields, trailingComma, close }: Fields))]
      [k := closed =>
        (let (fields, trailingComma) := bracedFieldsIn modes.inBrackets closed;
         let close := modes.inBrackets.expectFixed RBrace "`,` or `}`";
         ({ open = openTwin, fields, trailingComma, close }: Fields))]
      (followsAt modes.inBrackets RBrace)
      (closed =>
        Parse.followsThen (followsBracedFieldsIn rule modes.inBrackets closed) (pair pairTwin pairs =>
          match pair, pairTwin with
            | (fields, trailing), (twins, trailingTwin) =>
              Parse.followsMap
                [alike := FieldsAlike]
                (close => { open, fields, trailingComma = trailing, close })
                (close => { open = openTwin, fields = twins, trailingComma = trailingTwin, close })
                (close closeTwin closes =>
                  alikeFields open openTwin fields twins pairs.left trailing trailingTwin pairs.right close closeTwin)
                (followsExpectFixed modes.inBrackets RBrace "`,` or `}`"))))

-- Facts read off alike groups.

theorem groupWalkAuto ∀ (group: Group): (group.walk blankPure).blank.auto = blankComments group.auto := match group with
  | { kind, implicit, open, attributes, auto, names, colon, annotation, default, close, bare } => byComputing

theorem groupWalkNames ∀ (group: Group): (group.walk blankPure).blank.names = blankWords group.names := match group with
  | { kind, implicit, open, attributes, auto, names, colon, annotation, default, close, bare } => byComputing

theorem blankCommentsSome ∀ (found: Option Comments): (blankComments found).isSome = found.isSome := match found with
  | Some _ | None => byComputing

theorem blankWordsEmpty ∀ (words: List Word): (blankWords words).isEmpty = words.isEmpty := match words with
  | [] | [_, .._] => byComputing

theorem groupAutoSome ∀ (group twin: Group) (alike: GroupsAlike group twin): group.auto.isSome = twin.auto.isSome :=
  let same: blankComments group.auto = blankComments twin.auto := calc blankComments group.auto
    _ = (group.walk blankPure).blank.auto := Eq.flipped (groupWalkAuto group)
    _ = (twin.walk blankPure).blank.auto := Eq.cong (found => found.auto) alike
    _ = blankComments twin.auto := groupWalkAuto twin
  calc group.auto.isSome
    _ = (blankComments group.auto).isSome := Eq.flipped (blankCommentsSome group.auto)
    _ = (blankComments twin.auto).isSome := rewrite same
    _ = twin.auto.isSome := blankCommentsSome twin.auto

theorem isNoneOfAlikeSome ∀ (found twin: Option Comments)
    (same: found.isSome = twin.isSome):
    found.isNone = twin.isNone :=
  match found, twin with
    | Some x, Some y => byComputing
    | None, None => byComputing

theorem groupNamesEmpty ∀ (group twin: Group)
    (alike: GroupsAlike group twin):
    group.names.isEmpty = twin.names.isEmpty :=
  let same: blankWords group.names = blankWords twin.names := calc blankWords group.names
    _ = (group.walk blankPure).blank.names := Eq.flipped (groupWalkNames group)
    _ = (twin.walk blankPure).blank.names := Eq.cong (found => found.names) alike
    _ = blankWords twin.names := groupWalkNames twin
  calc group.names.isEmpty
    _ = (blankWords group.names).isEmpty := Eq.flipped (blankWordsEmpty group.names)
    _ = (blankWords twin.names).isEmpty := rewrite same
    _ = twin.names.isEmpty := blankWordsEmpty twin.names

-- Look-aheads that read the count of items left.

theorem followsBracketAhead ∀ (modes: Modes):
    Parse.Follows SameCode Same (() => modes.at LBracket && implicitBinderAhead (Parse.mark().left + 1) left()) (() =>
      modes.at LBracket && implicitBinderAhead (Parse.mark().left + 1) left()) :=
  followsThenEq (followsAt modes LBracket) (here =>
    match here with
      | True => followsFuel (fuel => implicitBinderAhead fuel left()) (fuel => implicitBinderAhead fuel left()) (fuel =>
        followsLook (implicitBinderAhead fuel) (implicitBinderAheadDeaf fuel))
      | False => Parse.followsDone False False byComputing)

theorem followsParenAhead ∀ (modes: Modes):
    Parse.Follows SameCode Same (() => isSome LParen modes.peek && piBinderAhead left()) (() =>
      isSome LParen modes.peek && piBinderAhead left()) :=
  followsThenEq
    [j := seen => isSome LParen seen && piBinderAhead left()]
    [k := seen => isSome LParen seen && piBinderAhead left()]
    (followsPeek modes)
    (seen =>
      match isSome LParen seen with
        | True => followsLook piBinderAhead piBinderAheadDeaf
        | False => Parse.followsDone False False byComputing)

-- Constructors.

def ConstructorPartsFollow (modes: Modes) (name nameTwin: Word) (fuel: Nat): Prop :=
  ∀ (bracketed braced: Bool) (found twins: List ConstructorPart) => List.All2 PartAlike found twins
    → Parse.Follows SameCode
      (List.All2 PartAlike)
      (() => constructorParts fuel modes name bracketed braced found)
      (() => constructorParts fuel modes nameTwin bracketed braced twins)

theorem followsConstructorBracket ∀ (rule: ExpressionRule) (more: Nat) (modes: Modes) (name nameTwin: Word)
    (again: ConstructorPartsFollow modes name nameTwin more)
    (bracketed braced: Bool) (found twins: List ConstructorPart)
    (founds: List.All2 PartAlike found twins) (bracket: Bool):
    Parse.Follows SameCode
      (List.All2 PartAlike)
      (() => constructorBracket more modes name bracketed braced found bracket)
      (() => constructorBracket more modes nameTwin bracketed braced twins bracket) :=
  match bracket with
    | True => Parse.followsThen (followsImplicitBinder (expressionKnot rule) modes) (binder binderTwin binders =>
      let autos: binder.auto.isSome = binderTwin.auto.isSome := groupAutoSome binder binderTwin binders
      rewrite autos then
        match binderTwin.auto.isSome with
          | True => followsFatalAny _ (() => Syntax.fatal "a constructor's implicit fields can't be `auto`")
          | False =>
            again bracketed braced
              [PartGroup binder, ..found]
              [PartGroup binderTwin, ..twins]
              (Both (alikePartGroup binder binderTwin binders) founds))
    | False => Parse.followsDone _ _ (List.all2Reverse found twins founds)

theorem followsConstructorParen ∀ (rule: ExpressionRule) (more: Nat) (modes: Modes) (name nameTwin: Word)
    (again: ConstructorPartsFollow modes name nameTwin more)
    (bracketed braced: Bool) (found twins: List ConstructorPart)
    (founds: List.All2 PartAlike found twins) (paren: Bool):
    Parse.Follows SameCode
      (List.All2 PartAlike)
      (() => constructorParen more modes name bracketed braced found paren)
      (() => constructorParen more modes nameTwin bracketed braced twins paren) :=
  match paren with
    | True =>
      match braced with
        | True => followsFatalAny _ (() =>
          Syntax.fatal
            "`${nameTwin.text}` has its fields in braces already; declare all of its explicit fields in braces or all in brackets")
        | False => Parse.followsThen (followsBinderGroup (expressionKnot rule) modes True) (binder binderTwin binders =>
          again True braced
            [PartGroup binder, ..found]
            [PartGroup binderTwin, ..twins]
            (Both (alikePartGroup binder binderTwin binders) founds))
    | False => followsThenEq (followsBracketAhead modes) (ahead =>
      followsConstructorBracket rule more modes name nameTwin again bracketed braced found twins founds ahead)

theorem followsConstructorBraced ∀ (rule: ExpressionRule) (more: Nat) (modes: Modes) (name nameTwin: Word)
    (again: ConstructorPartsFollow modes name nameTwin more)
    (bracketed braced: Bool) (found twins: List ConstructorPart)
    (founds: List.All2 PartAlike found twins) (brace: Bool):
    Parse.Follows SameCode
      (List.All2 PartAlike)
      (() => constructorBraced more modes name bracketed braced found brace)
      (() => constructorBraced more modes nameTwin bracketed braced twins brace) :=
  match brace with
    | True =>
      match bracketed with
        | True => followsFatalAny _ (() =>
          Syntax.fatal
            "`${nameTwin.text}` has fields in brackets already; declare all of its explicit fields in brackets or all in braces")
        | False => Parse.followsThen (followsBracedFields rule modes) (fields fieldsTwin fieldses =>
          let empties: fields.fields.isEmpty = fieldsTwin.fields.isEmpty := fieldsEmpty fields fieldsTwin fieldses
          rewrite empties then
            match fieldsTwin.fields.isEmpty with
              | True => followsFatalAny _ (() => Syntax.fatal "`${nameTwin.text}` declares no fields in its braces")
              | False =>
                again False True
                  [PartFields fields, ..found]
                  [PartFields fieldsTwin, ..twins]
                  (Both (alikePartFields fields fieldsTwin fieldses) founds))
    | False => followsThenEq (followsAt modes LParen) (paren =>
      followsConstructorParen rule more modes name nameTwin again bracketed braced found twins founds paren)

theorem followsConstructorParts ∀ (rule: ExpressionRule) (fuel: Nat) (modes: Modes) (name nameTwin: Word)
    (bracketed braced: Bool) (found twins: List ConstructorPart)
    (founds: List.All2 PartAlike found twins):
    Parse.Follows SameCode (List.All2 PartAlike) (() => constructorParts fuel modes name bracketed braced found) (() =>
      constructorParts fuel modes nameTwin bracketed braced twins) :=
  match fuel with
    | Succ more =>
      followsThenEq
        [j := brace => constructorBraced more modes name bracketed braced found (brace && !braced)]
        [k := brace => constructorBraced more modes nameTwin bracketed braced twins (brace && !braced)]
        (followsAt modes LBrace)
        (brace =>
          followsConstructorBraced rule more modes name nameTwin
            (again1 again2 agains3 agains4 agains5 =>
              followsConstructorParts rule more modes name nameTwin again1 again2 agains3 agains4 agains5)
            bracketed
            braced
            found
            twins
            founds
            (brace && !braced))
    | Zero => Parse.followsDone _ _ (List.all2Reverse found twins founds)

theorem followsConstructorResult ∀ (rule: ExpressionRule) (modes: Modes) (atColon: Bool):
    Parse.Follows SameCode (Option.Alike (PairAlike Anything ExprsAlike)) (() => constructorResult modes atColon) (() =>
      constructorResult modes atColon) :=
  match atColon with
    | True => Parse.followsThen followsFixedFrom (colon colonTwin colons =>
      Parse.followsMap
        (result => Some (colon, result))
        (result => Some (colonTwin, result))
        (result resultTwin results => (colons, results))
        (followsExpressionAt rule { modes, level = LevelApp }))
    | False => Parse.followsDone None None Trivial

theorem followsConstructorStep ∀ (rule: ExpressionRule) (modes: Modes) (atBar: Bool):
    Parse.Follows SameCode (Option.Alike ConstructorAlike) (() => constructorStep modes atBar) (() =>
      constructorStep modes atBar) :=
  match atBar with
    | True => Parse.followsThen followsFixedFrom (bar barTwin bars =>
      Parse.followsThen (followsAttributesOf modes) (attributes attributesTwin attributeses =>
        Parse.followsThen
          (followsUpper modes "a constructor name (starting with an uppercase letter)")
          (name nameTwin names =>
            followsFuel
              (fuel =>
                (let fields := constructorParts fuel modes name False False [];
                 let result := constructorResult modes (modes.at Colon);
                 Some { bar, attributes, name, fields, result }))
              (fuel =>
                (let fields := constructorParts fuel modes nameTwin False False [];
                 let result := constructorResult modes (modes.at Colon);
                 Some { bar = barTwin, attributes = attributesTwin, name = nameTwin, fields, result }))
              (fuel =>
                Parse.followsThen
                  (followsConstructorParts rule fuel modes name nameTwin False False [] [] Trivial)
                  (fields fieldsTwin fieldses =>
                    followsThenEq (followsAt modes Colon) (atColon =>
                      Parse.followsMap
                        (result => Some { bar, attributes, name, fields, result })
                        (result =>
                          Some {
                            bar = barTwin,
                            attributes = attributesTwin,
                            name = nameTwin,
                            fields = fieldsTwin,
                            result
                          })
                        (result resultTwin results =>
                          alikeConstructor bar barTwin attributes attributesTwin attributeses name nameTwin names fields
                              fieldsTwin fieldses result resultTwin results)
                        (followsConstructorResult rule modes atColon)))))))
    | False => Parse.followsDone None None Trivial

theorem followsConstructorsAt ∀ (rule: ExpressionRule) (modes: Modes) (atBar: Bool):
    Parse.Follows SameCode (List.All2 ConstructorAlike) (() => constructorsAt modes atBar) (() =>
      constructorsAt modes atBar) :=
  match atBar with
    | True =>
      Parse.followsLoop _ _ (followsThenEq (followsAt modes Pipe) (bar => followsConstructorStep rule modes bar))
    | False => followsFail modes "`|` and a constructor, or `{` and a record's fields" (() =>
      modes.fail "`|` and a constructor, or `{` and a record's fields")

theorem followsConstructorsOf ∀ (rule: ExpressionRule) (modes: Modes):
    Parse.Follows SameCode (List.All2 ConstructorAlike) (() => constructorsOf modes) (() => constructorsOf modes) :=
  followsThenEq (followsAt modes Pipe) (atBar => followsConstructorsAt rule modes atBar)

-- Data parameters and indices.

theorem followsDataParamLeft ∀ (modes: Modes) (word: Text) (items others: List Item)
    (same: List.All2 SameCode items others):
    Parse.Follows SameCode (Option.Alike GroupsAlike) (() => dataParamLeft modes word items) (() =>
      dataParamLeft modes word others) :=
  match items, others with
    | [param, ..rest], [paramTwin, ..restTwin] =>
      let kinds: param.kind = paramTwin.kind := deafItem Item.kind itemKindDeaf param paramTwin same.left
      let quals: isQualified param = isQualified paramTwin :=
        deafItem isQualified isQualifiedDeaf param paramTwin same.left
      let stops: modes.stops param = modes.stops paramTwin := stopsSame modes param paramTwin same.left
      let guards: (param.kind == Lower && !isQualified param && !modes.stops param)
        = (paramTwin.kind == Lower && !isQualified paramTwin && !modes.stops paramTwin) :=
        rewrite stops, quals, kinds
      match first: param.kind == Lower && !isQualified param && !modes.stops param, second: paramTwin.kind == Lower
        && !isQualified paramTwin
        && !modes.stops paramTwin with
        | True, True =>
          followsFatalAny _ (() => Syntax.fatal "a ${word}'s parameter `${paramTwin.text}` needs its type, in brackets")
        | False, False => Parse.followsDone None None Trivial
    | [], [] => Parse.followsDone None None Trivial

theorem followsDataParamBracket ∀ (rule: ExpressionRule) (modes: Modes) (word: Text) (bracket: Bool):
    Parse.Follows SameCode (Option.Alike GroupsAlike) (() => dataParamBracket modes word bracket) (() =>
      dataParamBracket modes word bracket) :=
  match bracket with
    | True => Parse.followsThen (followsImplicitBinder (expressionKnot rule) modes) (binder binderTwin binders =>
      Parse.followsThen
        (followsRefuseEmpty binder.attributes binderTwin.attributes
          (groupAttributesEmpty binder binderTwin binders)
          "a data type's parameter")
        (refusal refusalTwin refusals =>
          let autos: binder.auto.isNone = binderTwin.auto.isNone :=
            isNoneOfAlikeSome binder.auto binderTwin.auto (groupAutoSome binder binderTwin binders)
          let names: binder.names.isEmpty = binderTwin.names.isEmpty := groupNamesEmpty binder binderTwin binders
          rewrite autos, names then
            match binderTwin.auto.isNone with
              | True => followsFatalAny _ (() =>
                Syntax.fatal "a type's parameters in brackets must be `auto`, like `[auto ord: Ord k]`")
              | False =>
                match binderTwin.names.isEmpty with
                  | True => followsFatalAny _ (() =>
                    Syntax.fatal
                        "a type's `auto` parameter needs a name, so it can be given by name: `[auto ord: Ord k]`")
                  | False => Parse.followsDone (Some binder) (Some binderTwin) binders))
    | False =>
      followsOn
        (items => dataParamLeft modes word items)
        (items => dataParamLeft modes word items)
        (itemList others same => followsDataParamLeft modes word itemList others same)

theorem followsDataParamStep ∀ (rule: ExpressionRule) (modes: Modes) (word: Text) (atParen: Bool):
    Parse.Follows SameCode (Option.Alike GroupsAlike) (() => dataParamStep modes word atParen) (() =>
      dataParamStep modes word atParen) :=
  match atParen with
    | True => Parse.followsThen (followsBinderGroup (expressionKnot rule) modes False) (binder binderTwin binders =>
      Parse.followsThen
        (followsRefuseEmpty binder.attributes binderTwin.attributes
          (groupAttributesEmpty binder binderTwin binders)
          "a data type's parameter")
        (refusal refusalTwin refusals => Parse.followsDone (Some binder) (Some binderTwin) binders))
    | False => followsThenEq (followsBracketAhead modes) (bracket => followsDataParamBracket rule modes word bracket)

theorem followsDataParams ∀ (rule: ExpressionRule) (modes: Modes) (word: Text) (name nameTwin: Word):
    Parse.Follows SameCode (List.All2 GroupsAlike) (() => dataParams modes word name) (() =>
      dataParams modes word nameTwin) :=
  Parse.followsLoop _ _
    (followsThenEq (followsAt modes LParen) (atParen => followsDataParamStep rule modes word atParen))

def IndicesFollow (modes: Modes) (fuel: Nat): Prop :=
  ∀ (found twins: List (Index, Word)) => List.All2 IndexStepAlike found twins
    → Parse.Follows SameCode
      (PairAlike (List.All2 IndexStepAlike) ExprsAlike)
      (() => dataIndices fuel modes found)
      (() => dataIndices fuel modes twins)

theorem followsDataIndexNext ∀ (rule: ExpressionRule) (more: Nat) (modes: Modes)
    (again: IndicesFollow modes more) (found twins: List (Index, Word))
    (founds: List.All2 IndexStepAlike found twins) (index indexTwin: Expr)
    (indexes: ExprsAlike index indexTwin) (atArrow: Bool):
    Parse.Follows SameCode
      (PairAlike (List.All2 IndexStepAlike) ExprsAlike)
      (() => dataIndexNext more modes found index atArrow)
      (() => dataIndexNext more modes twins indexTwin atArrow) :=
  match atArrow with
    | True => Parse.followsThen followsBump (arrow arrowTwin arrows =>
      again
        [(IndexType index, arrow), ..found]
        [(IndexType indexTwin, arrowTwin), ..twins]
        (Both (alikeStepType index indexTwin indexes arrow arrowTwin arrows) founds))
    | False => Parse.followsDone _ _ (List.all2Reverse found twins founds, indexes)

theorem followsDataIndexAt ∀ (rule: ExpressionRule) (more: Nat) (modes: Modes)
    (again: IndicesFollow modes more) (found twins: List (Index, Word))
    (founds: List.All2 IndexStepAlike found twins) (paren: Bool):
    Parse.Follows SameCode
      (PairAlike (List.All2 IndexStepAlike) ExprsAlike)
      (() => dataIndexAt more modes found paren)
      (() => dataIndexAt more modes twins paren) :=
  match paren with
    | True => Parse.followsThen (followsBinderGroup (expressionKnot rule) modes False) (binder binderTwin binders =>
      Parse.followsThen
        (followsRefuseEmpty binder.attributes binderTwin.attributes
          (groupAttributesEmpty binder binderTwin binders)
          "a data type's index")
        (refusal refusalTwin refusals =>
          Parse.followsThen (followsExpect modes Arrow "`->`") (arrow arrowTwin arrows =>
            again
              [(IndexBinder binder, arrow), ..found]
              [(IndexBinder binderTwin, arrowTwin), ..twins]
              (Both (alikeStepBinder binder binderTwin binders arrow arrowTwin arrows) founds))))
    | False => Parse.followsThen (followsExpressionAt rule { modes, level = LevelApp }) (index indexTwin indexes =>
      followsThenEq (followsAt modes Arrow) (atArrow =>
        followsDataIndexNext rule more modes again found twins founds index indexTwin indexes atArrow))

theorem followsDataIndices ∀ (rule: ExpressionRule) (fuel: Nat) (modes: Modes) (found twins: List (Index, Word))
    (founds: List.All2 IndexStepAlike found twins):
    Parse.Follows SameCode (PairAlike (List.All2 IndexStepAlike) ExprsAlike) (() => dataIndices fuel modes found) (() =>
      dataIndices fuel modes twins) :=
  match fuel with
    | Zero => followsFatalAny _ (() => Syntax.fatal "the parser ran out of fuel in a data type's indices")
    | Succ more => followsThenEq (followsParenAhead modes) (paren =>
      followsDataIndexAt rule more modes
        (again twinsAgain agains => followsDataIndices rule more modes again twinsAgain agains)
        found
        twins
        founds
        paren)

-- Types and data declarations.

theorem annotatedAlike ∀ (expr twin: Expr)
    (alike: ExprsAlike expr twin):
    annotatedArgument expr = annotatedArgument twin :=
  calc annotatedArgument expr
    _ = annotatedArgument (expr.walk blankPure) := annotatedArgumentDeaf expr
    _ = annotatedArgument (twin.walk blankPure) := rewrite alike
    _ = annotatedArgument twin := Eq.flipped (annotatedArgumentDeaf twin)

theorem followsTypeSynonym ∀ (rule: ExpressionRule) (modes: Modes) (name nameTwin: Word):
    Parse.Follows SameCode ExprsAlike (() => typeSynonym modes name) (() => typeSynonym modes nameTwin) :=
  Parse.followsThen (followsExpressionAt rule { modes, level = LevelFull }) (synonym synonymTwin synonyms =>
    followsThenEq (followsAt modes Pipe) (atPipe =>
      match atPipe with
        | True =>
          followsFatalAny _ (() => Syntax.fatal (ambiguousSynonym nameTwin "a sum type without its leading `|`"))
        | False =>
          rewrite annotatedAlike synonym synonymTwin synonyms then
            match annotatedArgument synonymTwin with
              | True => followsFatalAny _ (() =>
                Syntax.fatal (ambiguousSynonym nameTwin "a constructor with named fields, without its leading `|`"))
              | False => Parse.followsDone synonym synonymTwin synonyms))

theorem followsTypeBraced ∀ (rule: ExpressionRule) (modes: Modes) (attributes attributesTwin: List Attributes)
    (attributeses: List.All2 AttributeGroupAlike attributes attributesTwin)
    (keyword keywordTwin: Comments) (name nameTwin: Word)
    (names: WordsAlike name nameTwin) (params paramsTwin: List Group)
    (paramses: List.All2 GroupsAlike params paramsTwin) (indices indicesTwin: Option Indices)
    (indiceses: IndicesAlike indices indicesTwin)
    (equals equalsTwin: Comments) (row: Option Text):
    Parse.Follows SameCode DeclsAlike (() => typeBraced modes attributes keyword name params indices equals row) (() =>
      typeBraced modes attributesTwin keywordTwin nameTwin paramsTwin indicesTwin equalsTwin row) :=
  match row with
    | Some found => followsFatalAny _ (() =>
      Syntax.fatal
        "an ability row like `{${found}}` can't be given a name with `type` yet; write the row where it's used, such as `() -> {${found}} Nat`")
    | None =>
      Parse.followsMap
        (fields => Data attributes False keyword name params indices (RecordBody equals fields))
        (fields => Data attributesTwin False keywordTwin nameTwin paramsTwin indicesTwin (RecordBody equalsTwin fields))
        (fields fieldsTwin fieldses =>
          alikeData attributes attributesTwin attributeses False keyword keywordTwin name nameTwin names params
              paramsTwin paramses indices indicesTwin indiceses
              (RecordBody equals fields)
              (RecordBody equalsTwin fieldsTwin)
              (alikeRecordBody equals equalsTwin fields fieldsTwin fieldses))
        (followsBracedFields rule modes)

theorem stepsEmpty ∀ (steps: List (Index, Word)):
    (blankIndexSteps (walkIndices blankPure steps)).isEmpty = steps.isEmpty :=
  match steps with | [] | [(IndexBinder _, _), .._] | [(IndexType _, _), .._] => byComputing

theorem indexedKey ∀ (indices: Option Indices):
    (indices.map (found => !found.steps.isEmpty) |> .getOrElse False)
      = ((indicesKey indices).map (found => !found.steps.isEmpty) |> .getOrElse False) :=
  match indices with
    | None => byComputing
    | Some { colon, steps, last } => rewrite stepsEmpty steps

theorem indexedAlike ∀ (indices indicesTwin: Option Indices)
    (indiceses: IndicesAlike indices indicesTwin):
    (indices.map (found => !found.steps.isEmpty) |> .getOrElse False)
      = (indicesTwin.map (found => !found.steps.isEmpty) |> .getOrElse False) :=
  calc (indices.map (found => !found.steps.isEmpty) |> .getOrElse False)
    _ = ((indicesKey indices).map (found => !found.steps.isEmpty) |> .getOrElse False) := indexedKey indices
    _ = ((indicesKey indicesTwin).map (found => !found.steps.isEmpty) |> .getOrElse False) := rewrite indiceses
    _ = (indicesTwin.map (found => !found.steps.isEmpty) |> .getOrElse False) := Eq.flipped (indexedKey indicesTwin)

theorem followsTypeAfterEquals ∀ (rule: ExpressionRule) (modes: Modes) (attributes attributesTwin: List Attributes)
    (attributeses: List.All2 AttributeGroupAlike attributes attributesTwin)
    (keyword keywordTwin: Comments) (name nameTwin: Word)
    (names: WordsAlike name nameTwin) (params paramsTwin: List Group)
    (paramses: List.All2 GroupsAlike params paramsTwin) (indices indicesTwin: Option Indices)
    (indiceses: IndicesAlike indices indicesTwin)
    (indexed: Bool) (equals equalsTwin: Comments) (brace pipe: Bool):
    Parse.Follows SameCode DeclsAlike
      (() => typeAfterEquals modes attributes keyword name params indices indexed equals brace pipe)
      (() =>
        typeAfterEquals modes attributesTwin keywordTwin nameTwin paramsTwin indicesTwin indexed equalsTwin brace
            pipe) :=
  match !(brace || pipe) with
    | True =>
      match indexed with
        | True => followsFatalAny _ (() =>
          Syntax.fatal "a type synonym can't have indices: `->` after the colon is only for a data type's indices")
        | False => Parse.followsThen (followsTypeSynonym rule modes name nameTwin) (synonym synonymTwin synonyms =>
          Parse.followsDone _ _
            (alikeData attributes attributesTwin attributeses False keyword keywordTwin name nameTwin names params
                paramsTwin paramses indices indicesTwin indiceses
                (Synonym equals synonym)
                (Synonym equalsTwin synonymTwin)
                (alikeSynonym equals equalsTwin synonym synonymTwin synonyms)))
    | False =>
      match brace with
        | True =>
          followsOn
            (items => typeBraced modes attributes keyword name params indices equals (abilityRowInBraces items))
            (items =>
              typeBraced modes attributesTwin keywordTwin nameTwin paramsTwin indicesTwin equalsTwin
                (abilityRowInBraces items))
            (itemList others same =>
              rewrite deafOfStripped abilityRowInBraces abilityRowInBracesDeaf itemList others same then
                followsTypeBraced rule modes attributes attributesTwin attributeses keyword keywordTwin name nameTwin
                    names params paramsTwin paramses indices indicesTwin indiceses equals equalsTwin
                    (abilityRowInBraces others))
        | False => Parse.followsThen (followsConstructorsOf rule modes) (constructors constructorsTwin constructorses =>
          Parse.followsDone _ _
            (alikeData attributes attributesTwin attributeses False keyword keywordTwin name nameTwin names params
                paramsTwin paramses indices indicesTwin indiceses
                (Sum equals constructors)
                (Sum equalsTwin constructorsTwin)
                (alikeSum equals equalsTwin constructors constructorsTwin constructorses)))

theorem followsTypeBody ∀ (rule: ExpressionRule) (modes: Modes) (attributes attributesTwin: List Attributes)
    (attributeses: List.All2 AttributeGroupAlike attributes attributesTwin)
    (keyword keywordTwin: Comments) (name nameTwin: Word)
    (names: WordsAlike name nameTwin) (params paramsTwin: List Group)
    (paramses: List.All2 GroupsAlike params paramsTwin) (indices indicesTwin: Option Indices)
    (indiceses: IndicesAlike indices indicesTwin) (indexed equalsNext: Bool):
    Parse.Follows SameCode DeclsAlike
      (() => typeBody modes attributes keyword name params indices indexed equalsNext)
      (() => typeBody modes attributesTwin keywordTwin nameTwin paramsTwin indicesTwin indexed equalsNext) :=
  match !equalsNext with
    | True =>
      Parse.followsDone _ _
        (alikeData attributes attributesTwin attributeses False keyword keywordTwin name nameTwin names params
            paramsTwin paramses indices indicesTwin indiceses Abstract Abstract alikeAbstract)
    | False => Parse.followsThen followsFixedFrom (equals equalsTwin equalses =>
      followsThenEq
        [j := brace =>
          typeAfterEquals modes attributes keyword name params indices indexed equals brace (modes.at Pipe)]
        [k := brace =>
          typeAfterEquals modes attributesTwin keywordTwin nameTwin paramsTwin indicesTwin indexed equalsTwin brace
            (modes.at Pipe)]
        (followsAt modes LBrace)
        (brace =>
          followsThenEq (followsAt modes Pipe) (pipe =>
            followsTypeAfterEquals rule modes attributes attributesTwin attributeses keyword keywordTwin name nameTwin
                names params paramsTwin paramses indices indicesTwin indiceses indexed equals equalsTwin brace pipe)))

theorem followsTypeDecl ∀ (rule: ExpressionRule) (modes: Modes) (attributes attributesTwin: List Attributes)
    (attributeses: List.All2 AttributeGroupAlike attributes attributesTwin)
    (keyword keywordTwin: Comments) (name nameTwin: Word)
    (names: WordsAlike name nameTwin) (params paramsTwin: List Group)
    (paramses: List.All2 GroupsAlike params paramsTwin) (indices indicesTwin: Option Indices)
    (indiceses: IndicesAlike indices indicesTwin) (indexed: Bool):
    Parse.Follows SameCode DeclsAlike (() => typeDecl modes attributes keyword name params indices indexed) (() =>
      typeDecl modes attributesTwin keywordTwin nameTwin paramsTwin indicesTwin indexed) :=
  followsThenEq (followsAt modes Equals) (equalsNext =>
    followsTypeBody rule modes attributes attributesTwin attributeses keyword keywordTwin name nameTwin names params
        paramsTwin paramses indices indicesTwin indiceses indexed equalsNext)

theorem followsInterfaceFields ∀ (rule: ExpressionRule) (modes: Modes) (attributes attributesTwin: List Attributes)
    (attributeses: List.All2 AttributeGroupAlike attributes attributesTwin)
    (keyword keywordTwin: Comments) (name nameTwin: Word)
    (names: WordsAlike name nameTwin) (params paramsTwin: List Group)
    (paramses: List.All2 GroupsAlike params paramsTwin) (indices indicesTwin: Option Indices)
    (indiceses: IndicesAlike indices indicesTwin)
    (equals equalsTwin: Comments) (braced: Bool):
    Parse.Follows SameCode DeclsAlike
      (() => interfaceFields modes attributes keyword name params indices equals braced)
      (() => interfaceFields modes attributesTwin keywordTwin nameTwin paramsTwin indicesTwin equalsTwin braced) :=
  match !braced with
    | True => followsFail modes "`{` and the interface's fields" (() => modes.fail "`{` and the interface's fields")
    | False =>
      Parse.followsMap
        [alike := DeclsAlike]
        [p := () => bracedFields modes]
        [q := () => bracedFields modes]
        (fields => Data attributes True keyword name params indices (RecordBody equals fields))
        (fields => Data attributesTwin True keywordTwin nameTwin paramsTwin indicesTwin (RecordBody equalsTwin fields))
        (fields fieldsTwin fieldses =>
          alikeData attributes attributesTwin attributeses True keyword keywordTwin name nameTwin names params
              paramsTwin paramses indices indicesTwin indiceses
              (RecordBody equals fields)
              (RecordBody equalsTwin fieldsTwin)
              (alikeRecordBody equals equalsTwin fields fieldsTwin fieldses))
        (followsBracedFields rule modes)

theorem followsInterfaceDecl ∀ (rule: ExpressionRule) (modes: Modes) (attributes attributesTwin: List Attributes)
    (attributeses: List.All2 AttributeGroupAlike attributes attributesTwin)
    (keyword keywordTwin: Comments) (name nameTwin: Word)
    (names: WordsAlike name nameTwin) (params paramsTwin: List Group)
    (paramses: List.All2 GroupsAlike params paramsTwin) (indices indicesTwin: Option Indices)
    (indiceses: IndicesAlike indices indicesTwin) (indexed: Bool):
    Parse.Follows SameCode DeclsAlike (() => interfaceDecl modes attributes keyword name params indices indexed) (() =>
      interfaceDecl modes attributesTwin keywordTwin nameTwin paramsTwin indicesTwin indexed) :=
  match indexed with
    | True => followsFatalAny _ (() => Syntax.fatal "an interface can't have indices")
    | False =>
      Parse.followsThen
        (followsExpectFixed modes Equals "`=` and the interface's fields, `{ … }`")
        (equals equalsTwin equalses =>
          followsThenEq (followsAt modes LBrace) (braced =>
            followsInterfaceFields rule modes attributes attributesTwin attributeses keyword keywordTwin name nameTwin
                names params paramsTwin paramses indices indicesTwin indiceses equals equalsTwin braced))

theorem followsDataName ∀ (modes: Modes) (isInterface: Bool):
    Parse.Follows SameCode WordsAlike (() => dataName modes isInterface) (() => dataName modes isInterface) :=
  match isInterface with
    | True => followsUpperQualified modes "an interface name (starting with an uppercase letter)"
    | False => followsUpperQualified modes "a data type name (starting with an uppercase letter)"

theorem followsDataIndicesPart ∀ (rule: ExpressionRule) (modes: Modes) (atColon: Bool):
    Parse.Follows SameCode IndicesAlike (() => dataIndicesPart modes atColon) (() => dataIndicesPart modes atColon) :=
  match atColon with
    | True => Parse.followsThen followsFixedFrom (colon colonTwin colons =>
      followsFuel
        (fuel => (let (steps, last) := dataIndices fuel modes []; Some { colon, steps, last }))
        (fuel => (let (steps, last) := dataIndices fuel modes []; Some { colon = colonTwin, steps, last }))
        (fuel =>
          Parse.followsThen (followsDataIndices rule fuel modes [] [] Trivial) (pair pairTwin pairs =>
            match pair, pairTwin with
              | (steps, last), (twins, lastTwin) =>
                Parse.followsDone _ _ (alikeIndices colon colonTwin steps twins pairs.left last lastTwin pairs.right))))
    | False => Parse.followsDone None None byComputing

theorem followsDataDeclOn ∀ (rule: ExpressionRule) (modes: Modes) (attributes attributesTwin: List Attributes)
    (attributeses: List.All2 AttributeGroupAlike attributes attributesTwin) (isInterface: Bool):
    Parse.Follows SameCode DeclsAlike (() => dataDeclOn modes attributes isInterface) (() =>
      dataDeclOn modes attributesTwin isInterface) :=
  Parse.followsThen followsFixedFrom (keyword keywordTwin keywords =>
    Parse.followsThen (followsDataName modes isInterface) (name nameTwin names =>
      Parse.followsThen
        (followsDataParams rule modes (if isInterface then "interface" else "type") name nameTwin)
        (params paramsTwin paramses =>
          followsThenEq
            [j := atColon =>
              (let indices := dataIndicesPart modes atColon;
               if isInterface then
                 interfaceDecl modes attributes keyword name params indices
                   (indices.map (found => !found.steps.isEmpty) |> .getOrElse False)
               else
                 typeDecl modes attributes keyword name params indices
                   (indices.map (found => !found.steps.isEmpty) |> .getOrElse False))]
            [k := atColon =>
              (let indices := dataIndicesPart modes atColon;
               if isInterface then
                 interfaceDecl modes attributesTwin keywordTwin nameTwin paramsTwin indices
                   (indices.map (found => !found.steps.isEmpty) |> .getOrElse False)
               else
                 typeDecl modes attributesTwin keywordTwin nameTwin paramsTwin indices
                   (indices.map (found => !found.steps.isEmpty) |> .getOrElse False))]
            (followsAt modes Colon)
            (atColon =>
              Parse.followsThen (followsDataIndicesPart rule modes atColon) (indices indicesTwin indiceses =>
                rewrite indexedAlike indices indicesTwin indiceses then
                  match isInterface with
                    | True =>
                      followsInterfaceDecl rule modes attributes attributesTwin attributeses keyword keywordTwin name
                          nameTwin names params paramsTwin paramses indices indicesTwin indiceses
                          (indicesTwin.map (found => !found.steps.isEmpty) |> .getOrElse False)
                    | False =>
                      followsTypeDecl rule modes attributes attributesTwin attributeses keyword keywordTwin name
                          nameTwin names params paramsTwin paramses indices indicesTwin indiceses
                          (indicesTwin.map (found => !found.steps.isEmpty) |> .getOrElse False))))))

theorem followsDataDecl ∀ (rule: ExpressionRule) (modes: Modes) (attributes attributesTwin: List Attributes)
    (attributeses: List.All2 AttributeGroupAlike attributes attributesTwin):
    Parse.Follows SameCode DeclsAlike (() => dataDecl modes attributes) (() => dataDecl modes attributesTwin) :=
  followsThenEq (followsAt modes KwInterface) (isInterface =>
    followsDataDeclOn rule modes attributes attributesTwin attributeses isInterface)

-- Abilities, tests and rule sets.

theorem followsOperation ∀ (rule: ExpressionRule) (modes: Modes):
    Parse.Follows SameCode OperationAlike (() => operation modes) (() => operation modes) :=
  followsThenEq followsOffset (here =>
    Parse.followsThen (followsLower { modes | allow = Some here } "an operation name") (name nameTwin names =>
      Parse.followsThen (followsExpectFixed { modes | allow = Some here } Colon "`:`") (colon colonTwin colons =>
        Parse.followsMap
          (annotation => { name, colon, annotation })
          (annotation => { name = nameTwin, colon = colonTwin, annotation })
          (annotation annotationTwin annotations =>
            alikeOperation name nameTwin names colon colonTwin annotation annotationTwin annotations)
          (followsExpressionAt rule { modes = { modes | allow = Some here }, level = LevelInline }))))

theorem followsOperationNext ∀ (rule: ExpressionRule) (modes: Modes) (column: Nat) (items others: List Item)
    (same: List.All2 SameCode items others):
    Parse.Follows SameCode (Option.Alike OperationAlike) (() => operationNext modes column items) (() =>
      operationNext modes column others) :=
  match items, others with
    | [next, ..rest], [nextTwin, ..restTwin] =>
      let tokens: next.leaf.token = nextTwin.leaf.token := itemToken next nextTwin same.left
      rewrite tokens then
        match nextTwin.leaf.token.lineStart && nextTwin.leaf.token.column == column with
          | True =>
            Parse.followsMap
              (found => Some found)
              (found => Some found)
              (x y alike => alike)
              (followsOperation rule modes)
          | False => Parse.followsDone None None Trivial
    | [], [] => Parse.followsDone None None Trivial

theorem followsOperations ∀ (rule: ExpressionRule) (modes: Modes) (column: Nat):
    Parse.Follows SameCode (List.All2 OperationAlike) (() => operations modes column) (() => operations modes column) :=
  Parse.followsThen (followsOperation rule modes) (first firstTwin firsts =>
    Parse.followsMap
      (rest => [first, ..rest])
      (rest => [firstTwin, ..rest])
      (rest restTwin rests => Both firsts rests)
      (Parse.followsLoop _ _
        (followsOn
          (items => operationNext modes column items)
          (items => operationNext modes column items)
          (itemList others same => followsOperationNext rule modes column itemList others same))))

theorem followsAbilityParamStep ∀ (rule: ExpressionRule) (modes: Modes) (atParen: Bool):
    Parse.Follows SameCode (Option.Alike GroupsAlike) (() => abilityParamStep modes atParen) (() =>
      abilityParamStep modes atParen) :=
  match atParen with
    | True => Parse.followsThen (followsBinderGroup (expressionKnot rule) modes False) (binder binderTwin binders =>
      Parse.followsThen
        (followsRefuseEmpty binder.attributes binderTwin.attributes
          (groupAttributesEmpty binder binderTwin binders)
          "an ability's parameter")
        (refusal refusalTwin refusals => Parse.followsDone (Some binder) (Some binderTwin) binders))
    | False => Parse.followsDone None None Trivial

theorem followsAbilityParams ∀ (rule: ExpressionRule) (modes: Modes):
    Parse.Follows SameCode (List.All2 GroupsAlike) (() => abilityParams modes) (() => abilityParams modes) :=
  Parse.followsLoop _ _ (followsThenEq (followsAt modes LParen) (atParen => followsAbilityParamStep rule modes atParen))

theorem followsAbilityOn ∀ (rule: ExpressionRule) (modes: Modes) (keyword keywordTwin: Comments) (name nameTwin: Word)
    (names: WordsAlike name nameTwin) (params paramsTwin: List Group)
    (paramses: List.All2 GroupsAlike params paramsTwin)
    (whereKeyword whereTwin: Comments) (seen: Option Tok) (items others: List Item)
    (same: List.All2 SameCode items others):
    Parse.Follows SameCode DeclsAlike (() => abilityOn modes keyword name params whereKeyword seen items) (() =>
      abilityOn modes keywordTwin nameTwin paramsTwin whereTwin seen others) :=
  match seen with
    | Some kind =>
      match items, others with
        | [first, ..rest], [firstTwin, ..restTwin] =>
          let tokens: first.leaf.token = firstTwin.leaf.token := itemToken first firstTwin same.left
          rewrite tokens then
            Parse.followsMap
              [alike := DeclsAlike]
              [p := () => operations { modes | limit = Some firstTwin.leaf.token.column } firstTwin.leaf.token.column]
              [q := () => operations { modes | limit = Some firstTwin.leaf.token.column } firstTwin.leaf.token.column]
              (found => Ability keyword name params whereKeyword found)
              (found => Ability keywordTwin nameTwin paramsTwin whereTwin found)
              (found foundTwin founds =>
                alikeAbility keyword keywordTwin name nameTwin names params paramsTwin paramses whereKeyword whereTwin
                    found foundTwin founds)
              (followsOperations rule { modes | limit = Some firstTwin.leaf.token.column } firstTwin.leaf.token.column)
        | [], [] => followsFail modes "the ability's operations" (() => modes.fail "the ability's operations")
    | None => followsFail modes "the ability's operations" (() => modes.fail "the ability's operations")

theorem followsAbilityDecl ∀ (rule: ExpressionRule) (modes: Modes):
    Parse.Follows SameCode DeclsAlike (() => abilityDecl modes) (() => abilityDecl modes) :=
  Parse.followsThen followsFixedFrom (keyword keywordTwin keywords =>
    Parse.followsThen
      (followsUpperQualified modes "an ability name (starting with an uppercase letter)")
      (name nameTwin names =>
        Parse.followsThen (followsAbilityParams rule modes) (params paramsTwin paramses =>
          Parse.followsThen (followsExpectFixed modes KwWhere "`where`") (whereKeyword whereTwin wheres =>
            followsThenEq (followsPeek modes) (seen =>
              followsOn
                (items => abilityOn modes keyword name params whereKeyword seen items)
                (items => abilityOn modes keywordTwin nameTwin paramsTwin whereTwin seen items)
                (itemList others same =>
                  followsAbilityOn rule modes keyword keywordTwin name nameTwin names params paramsTwin paramses
                      whereKeyword whereTwin seen itemList others same))))))

theorem followsTestAfterName ∀ (rule: ExpressionRule) (modes: Modes)
    (keyword keywordTwin: Comments) (name nameTwin: Word)
    (names: WordsAlike name nameTwin) (equalsNext: Bool):
    Parse.Follows SameCode DeclsAlike (() => testAfterName modes keyword name equalsNext) (() =>
      testAfterName modes keywordTwin nameTwin equalsNext) :=
  match equalsNext with
    | True => followsFatalAny _ _
    | False => Parse.followsThen (followsExpectFixed modes ColonEq "`:=`") (colonEq colonEqTwin colonEqs =>
      Parse.followsMap
        (body => Test keyword name colonEq body)
        (body => Test keywordTwin nameTwin colonEqTwin body)
        (body bodyTwin bodies =>
          alikeTest keyword keywordTwin name nameTwin names colonEq colonEqTwin body bodyTwin bodies)
        (followsExpressionAt rule { modes, level = LevelFull }))

theorem followsTestName ∀ (modes: Modes) (atStr: Bool):
    Parse.Follows SameCode WordsAlike (() => testName modes atStr) (() => testName modes atStr) :=
  match atStr with
    | True => followsBump
    | False => followsFail modes "the test's name, in quotes" (() => modes.fail "the test's name, in quotes")

theorem followsTestDecl ∀ (rule: ExpressionRule) (modes: Modes):
    Parse.Follows SameCode DeclsAlike (() => testDecl modes) (() => testDecl modes) :=
  Parse.followsThen followsFixedFrom (keyword keywordTwin keywords =>
    followsThenEq
      [j := atStr => (let name := testName modes atStr; testAfterName modes keyword name (modes.at Equals))]
      [k := atStr => (let name := testName modes atStr; testAfterName modes keywordTwin name (modes.at Equals))]
      (followsAt modes Str)
      (atStr =>
        Parse.followsThen (followsTestName modes atStr) (name nameTwin names =>
          followsThenEq (followsAt modes Equals) (equalsNext =>
            followsTestAfterName rule modes keyword keywordTwin name nameTwin names equalsNext))))

theorem followsRuleSetName ∀ (modes: Modes) (atUpper: Bool):
    Parse.Follows SameCode WordsAlike (() => ruleSetName modes atUpper) (() => ruleSetName modes atUpper) :=
  match atUpper with
    | True => followsUpperQualified modes "a name"
    | False => followsLowerQualified modes "a name"

theorem followsRuleSetOpen ∀ (rule: ExpressionRule) (modes: Modes) (keyword keywordTwin: Comments) (name nameTwin: Word)
    (names: WordsAlike name nameTwin)
    (colonEq colonEqTwin: Comments) (atBracket: Bool):
    Parse.Follows SameCode DeclsAlike (() => ruleSetOpen modes keyword name colonEq atBracket) (() =>
      ruleSetOpen modes keywordTwin nameTwin colonEqTwin atBracket) :=
  match atBracket with
    | True =>
      Parse.followsMap
        (rules => RuleSetDecl keyword name colonEq rules)
        (rules => RuleSetDecl keywordTwin nameTwin colonEqTwin rules)
        (rules rulesTwin ruleses =>
          alikeRuleSetDecl keyword keywordTwin name nameTwin names colonEq colonEqTwin rules rulesTwin ruleses)
        (followsRuleSet (expressionKnot rule) (modes wanted what => followsExpectFixed modes wanted what) modes)
    | False => followsFail modes "the set's rules, in brackets: `[r1, <- r2]`" (() =>
      modes.fail "the set's rules, in brackets: `[r1, <- r2]`")

theorem followsRuleSetAfterName ∀ (rule: ExpressionRule) (modes: Modes)
    (keyword keywordTwin: Comments) (name nameTwin: Word)
    (names: WordsAlike name nameTwin) (equalsNext: Bool):
    Parse.Follows SameCode DeclsAlike (() => ruleSetAfterName modes keyword name equalsNext) (() =>
      ruleSetAfterName modes keywordTwin nameTwin equalsNext) :=
  match equalsNext with
    | True => followsFatalAny _ _
    | False => Parse.followsThen (followsExpectFixed modes ColonEq "`:=`") (colonEq colonEqTwin colonEqs =>
      followsThenEq (followsAt modes LBracket) (atBracket =>
        followsRuleSetOpen rule modes keyword keywordTwin name nameTwin names colonEq colonEqTwin atBracket))

theorem followsRuleSetDecl ∀ (rule: ExpressionRule) (modes: Modes):
    Parse.Follows SameCode DeclsAlike (() => ruleSetDecl modes) (() => ruleSetDecl modes) :=
  Parse.followsThen followsFixedFrom (keyword keywordTwin keywords =>
    followsThenEq
      [j := atUpper => (let name := ruleSetName modes atUpper; ruleSetAfterName modes keyword name (modes.at Equals))]
      [k := atUpper =>
        (let name := ruleSetName modes atUpper; ruleSetAfterName modes keywordTwin name (modes.at Equals))]
      (followsAt modes Upper)
      (atUpper =>
        Parse.followsThen (followsRuleSetName modes atUpper) (name nameTwin names =>
          followsThenEq (followsAt modes Equals) (equalsNext =>
            followsRuleSetAfterName rule modes keyword keywordTwin name nameTwin names equalsNext))))

-- Definitions and instances.

theorem walkHeaderKind ∀ (header: Header): (walkHeader blankPure header).kind = header.kind := match header with
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
    } => byComputing

theorem headerKindAlike ∀ (header twin: Header) (alike: HeaderAlike header twin): header.kind = twin.kind :=
  calc header.kind
    _ = (walkHeader blankPure header).kind := Eq.flipped (walkHeaderKind header)
    _ = (walkHeader blankPure twin).kind := Eq.cong (found => found.kind) alike
    _ = twin.kind := walkHeaderKind twin

theorem followsDefinition ∀ (rule: ExpressionRule) (alts: AltPatternFollows)
    (modes: Modes) (attributes attributesTwin: List Attributes)
    (attributeses: List.All2 AttributeGroupAlike attributes attributesTwin)
    (exportKeyword exportTwin opaqueKeyword opaqueTwin: Option Comments)
    (exports: Option.Alike Anything exportKeyword exportTwin)
    (opaques: Option.Alike Anything opaqueKeyword opaqueTwin):
    Parse.Follows SameCode DeclsAlike (() => definition modes attributes exportKeyword opaqueKeyword) (() =>
      definition modes attributesTwin exportTwin opaqueTwin) :=
  Parse.followsThen
    (followsDefinitionParts
      (expressionKnot rule)
      alts
      modes
      exportKeyword
      exportTwin
      opaqueKeyword
      opaqueTwin
      exports
      opaques
      None)
    (parts partsTwin partses =>
      match parts, partsTwin with
        | (header, body), (headerTwin, bodyTwin) =>
          Parse.followsDone _ _
            (alikeDefinition attributes attributesTwin attributeses header headerTwin partses.left body bodyTwin
                partses.right))

theorem followsInstanceDecl ∀ (rule: ExpressionRule) (alts: AltPatternFollows)
    (modes: Modes) (attributes attributesTwin: List Attributes)
    (attributeses: List.All2 AttributeGroupAlike attributes attributesTwin):
    Parse.Follows SameCode DeclsAlike (() => instanceDecl modes attributes) (() => instanceDecl modes attributesTwin) :=
  Parse.followsThen
    (followsDefinitionParts (expressionKnot rule) alts modes None None None None Trivial Trivial None)
    (parts partsTwin partses =>
      match parts, partsTwin with
        | (header, body), (headerTwin, bodyTwin) =>
          let kinds: header.kind = headerTwin.kind := headerKindAlike header headerTwin partses.left
          rewrite kinds then
            match headerTwin.kind == DefInstance with
              | True =>
                Parse.followsDone _ _
                  (alikeDefinition attributes attributesTwin attributeses header headerTwin partses.left body bodyTwin
                      partses.right)
              | False => followsFatalAny _ _)

-- One declaration.

theorem followsAfterOpaqueOn ∀ (modes: Modes) (seen: Option Tok):
    Parse.Follows SameCode Anything (() => afterOpaqueOn modes seen) (() => afterOpaqueOn modes seen) :=
  match seen with
    | Some KwDef => Parse.followsDone () () Trivial
    | Some KwTheorem | Some KwInstance | Some KwExport => followsFatalAny _ _
    | _ => followsFail modes "`def` after `opaque`" (() => modes.fail "`def` after `opaque`")

theorem followsAfterOpaque ∀ (modes: Modes):
    Parse.Follows SameCode Anything (() => afterOpaque modes) (() => afterOpaque modes) :=
  followsPeeked modes (seen => afterOpaqueOn modes seen) (seen => afterOpaqueOn modes seen) (seen =>
    followsAfterOpaqueOn modes seen)

theorem followsRulesAhead ∀ (modes: Modes):
    Parse.Follows SameCode Same (() => wordAhead modes "rules" && isSome Lower (modes.peekAt 1)) (() =>
      wordAhead modes "rules" && isSome Lower (modes.peekAt 1)) :=
  followsThenEq (followsWordAhead modes "rules") (found =>
    match found with
      | True => followsThenEq (followsPeekAt modes 1) (second =>
        Parse.followsDone (isSome Lower second) (isSome Lower second) byComputing)
      | False => Parse.followsDone False False byComputing)

theorem followsRuleSetOrMissing ∀ (rule: ExpressionRule) (modes: Modes) (found: Bool):
    Parse.Follows SameCode DeclsAlike (() => ruleSetOrMissing modes found) (() => ruleSetOrMissing modes found) :=
  match found with
    | True => followsRuleSetDecl rule modes
    | False => followsFatalAny _ _

theorem followsExportPlain ∀ (rule: ExpressionRule) (alts: AltPatternFollows)
    (modes: Modes) (attributes attributesTwin: List Attributes)
    (attributeses: List.All2 AttributeGroupAlike attributes attributesTwin)
    (exported exportedTwin: Comments) (found: Bool):
    Parse.Follows SameCode DeclsAlike (() => exportPlain modes attributes exported found) (() =>
      exportPlain modes attributesTwin exportedTwin found) :=
  match found with
    | True =>
      followsDefinition rule alts modes attributes attributesTwin attributeses
        (Some exported)
        (Some exportedTwin)
        None
        None
        Trivial
        Trivial
    | False => followsFail modes "`def`, `theorem` or `opaque` after `export`" (() =>
      modes.fail "`def`, `theorem` or `opaque` after `export`")

theorem followsExportAfter ∀ (rule: ExpressionRule) (alts: AltPatternFollows)
    (modes: Modes) (attributes attributesTwin: List Attributes)
    (attributeses: List.All2 AttributeGroupAlike attributes attributesTwin)
    (exported exportedTwin: Comments) (atOpaque: Bool):
    Parse.Follows SameCode DeclsAlike (() => exportAfter modes attributes exported atOpaque) (() =>
      exportAfter modes attributesTwin exportedTwin atOpaque) :=
  match atOpaque with
    | True => Parse.followsThen followsFixedFrom (opaqued opaquedTwin opaqueds =>
      Parse.followsThen (followsAfterOpaque modes) (skippedItems skippedTwin skips =>
        followsDefinition rule alts modes attributes attributesTwin attributeses
          (Some exported)
          (Some exportedTwin)
          (Some opaqued)
          (Some opaquedTwin)
          Trivial
          Trivial))
    | False => followsThenEq (followsAtEither modes KwDef KwTheorem) (found =>
      followsExportPlain rule alts modes attributes attributesTwin attributeses exported exportedTwin found)

theorem followsDeclarationOther ∀ (rule: ExpressionRule) (alts: AltPatternFollows)
    (modes: Modes) (attributes attributesTwin: List Attributes)
    (attributeses: List.All2 AttributeGroupAlike attributes attributesTwin) (seen: Option Tok):
    Parse.Follows SameCode DeclsAlike (() => declarationOther modes attributes seen) (() =>
      declarationOther modes attributesTwin seen) :=
  match seen with
    | Some KwType | Some KwInterface => followsDataDecl rule modes attributes attributesTwin attributeses
    | Some KwInstance => followsInstanceDecl rule alts modes attributes attributesTwin attributeses
    | Some KwAbility => followsAbilityDecl rule modes
    | Some KwTest => followsTestDecl rule modes
    | Some KwExport => Parse.followsThen followsFixedFrom (exported exportedTwin exporteds =>
      followsThenEq (followsAt modes KwOpaque) (atOpaque =>
        followsExportAfter rule alts modes attributes attributesTwin attributeses exported exportedTwin atOpaque))
    | Some KwOpaque => Parse.followsThen followsFixedFrom (opaqued opaquedTwin opaqueds =>
      Parse.followsThen (followsAfterOpaque modes) (skippedItems skippedTwin skips =>
        followsDefinition rule alts modes attributes attributesTwin attributeses None None
          (Some opaqued)
          (Some opaquedTwin)
          Trivial
          Trivial))
    | Some Lower => followsThenEq (followsRulesAhead modes) (found => followsRuleSetOrMissing rule modes found)
    | Some Upper => followsFatalAny _ _
    | _ => followsFail modes "a declaration" (() => modes.fail "a declaration")

theorem followsDeclarationBodyOn ∀ (rule: ExpressionRule) (alts: AltPatternFollows)
    (modes: Modes) (attributes attributesTwin: List Attributes)
    (attributeses: List.All2 AttributeGroupAlike attributes attributesTwin) (seen: Option Tok):
    Parse.Follows SameCode DeclsAlike (() => declarationBodyOn modes attributes seen) (() =>
      declarationBodyOn modes attributesTwin seen) :=
  match seen with
    | Some kind =>
      match kind == KwDef || kind == KwTheorem with
        | True =>
          followsDefinition rule alts modes attributes attributesTwin attributeses None None None None Trivial Trivial
        | False => followsDeclarationOther rule alts modes attributes attributesTwin attributeses (Some kind)
    | None => followsDeclarationOther rule alts modes attributes attributesTwin attributeses None

theorem followsDeclarationBody ∀ (rule: ExpressionRule) (alts: AltPatternFollows)
    (modes: Modes) (attributes attributesTwin: List Attributes)
    (attributeses: List.All2 AttributeGroupAlike attributes attributesTwin):
    Parse.Follows SameCode DeclsAlike (() => declarationBody modes attributes) (() =>
      declarationBody modes attributesTwin) :=
  followsPeeked modes
    (seen => declarationBodyOn modes attributes seen)
    (seen => declarationBodyOn modes attributesTwin seen)
    (seen => followsDeclarationBodyOn rule alts modes attributes attributesTwin attributeses seen)

theorem followsNamespaceStep ∀ (seen: Seen) (modes: Modes):
    Parse.Follows SameCode DeclsAlike (() => namespaceStep seen modes) (() => namespaceStep seen modes) :=
  match seen.hasNamespace with
    | True => followsFatalAny _ (() => Syntax.fatal "a file has only one namespace line")
    | False =>
      match seen.hasImports || seen.hasDecls with
        | True =>
          followsFatalAny _ (() => Syntax.fatal "the namespace line must come first, before imports and declarations")
        | False => followsNamespaceLine modes

theorem followsImportStep ∀ (seen: Seen) (modes: Modes):
    Parse.Follows SameCode DeclsAlike (() => importStep seen modes) (() => importStep seen modes) :=
  match seen.hasDecls with
    | True => followsFatalAny _ (() => Syntax.fatal "imports go at the top of the file")
    | False => followsImportLine modes

theorem followsDeclarationKind ∀ (rule: ExpressionRule) (alts: AltPatternFollows) (seen: Seen)
    (modes: Modes) (attributes attributesTwin: List Attributes)
    (attributeses: List.All2 AttributeGroupAlike attributes attributesTwin) (next: Option Tok):
    Parse.Follows SameCode DeclsAlike (() => declarationKind seen modes attributes next) (() =>
      declarationKind seen modes attributesTwin next) :=
  match next with
    | Some kind =>
      match kind == KwNamespace with
        | True => followsNamespaceStep seen modes
        | False =>
          match kind == KwImport with
            | True => followsImportStep seen modes
            | False => followsDeclarationBody rule alts modes attributes attributesTwin attributeses
    | None => followsDeclarationBody rule alts modes attributes attributesTwin attributeses

theorem followsDeclarationEnd ∀ (modes: Modes) (decl declTwin: Decl)
    (decls: DeclsAlike decl declTwin) (items others: List Item)
    (same: List.All2 SameCode items others):
    Parse.Follows SameCode DeclsAlike (() => declarationEnd modes decl items) (() =>
      declarationEnd modes declTwin others) :=
  let empties: items.isEmpty = others.isEmpty := List.all2IsEmpty items others same
  rewrite empties then
    match others.isEmpty with
      | True => Parse.followsDone decl declTwin decls
      | False => followsFail modes "the end of the declaration" (() => modes.fail "the end of the declaration")

theorem followsDeclarationFinish ∀ (modes: Modes) (decl declTwin: Decl)
    (decls: DeclsAlike decl declTwin):
    Parse.Follows SameCode DeclsAlike (() => declarationFinish modes decl) (() => declarationFinish modes declTwin) :=
  followsOn
    (items => declarationEnd modes decl items)
    (items => declarationEnd modes declTwin items)
    (itemList others same => followsDeclarationEnd modes decl declTwin decls itemList others same)

theorem followsDeclarationRefusal ∀ (rule: ExpressionRule) (alts: AltPatternFollows) (seen: Seen)
    (modes: Modes) (attributes attributesTwin: List Attributes)
    (attributeses: List.All2 AttributeGroupAlike attributes attributesTwin) (next: Option Tok):
    Parse.Follows SameCode DeclsAlike (() => declarationRefusal seen modes attributes next) (() =>
      declarationRefusal seen modes attributesTwin next) :=
  let refused: attributesRefused attributes next = attributesRefused attributesTwin next := calc attributesRefused
      attributes next
    _ = attributesRefused (walkAttributes blankPure attributes) next := attributesRefusedDeaf attributes next
    _ = attributesRefused (walkAttributes blankPure attributesTwin) next :=
      rewrite walkAttributesAlike attributes attributesTwin attributeses
    _ = attributesRefused attributesTwin next := Eq.flipped (attributesRefusedDeaf attributesTwin next)
  rewrite refused then
    match attributesRefused attributesTwin next with
      | Some message => followsFatalAny _ (() => Syntax.fatal message)
      | None =>
        followsThenEq
          [j := kind => declarationFinish modes (declarationKind seen modes attributes kind)]
          [k := kind => declarationFinish modes (declarationKind seen modes attributesTwin kind)]
          (followsPeek modes)
          (kind =>
            Parse.followsThen
              (followsDeclarationKind rule alts seen modes attributes attributesTwin attributeses kind)
              (decl declTwin decls => followsDeclarationFinish modes decl declTwin decls))

theorem followsDeclarationAttributes ∀ (rule: ExpressionRule) (alts: AltPatternFollows) (seen: Seen)
    (modes: Modes) (attributes attributesTwin: List Attributes)
    (attributeses: List.All2 AttributeGroupAlike attributes attributesTwin):
    Parse.Follows SameCode DeclsAlike (() => declarationAttributes seen modes attributes) (() =>
      declarationAttributes seen modes attributesTwin) :=
  followsPeeked modes
    (next => declarationRefusal seen modes attributes next)
    (next => declarationRefusal seen modes attributesTwin next)
    (next => followsDeclarationRefusal rule alts seen modes attributes attributesTwin attributeses next)

theorem followsDeclaration ∀ (rule: ExpressionRule) (alts: AltPatternFollows) (seen: Seen):
    Parse.Follows SameCode DeclsAlike (() => declaration seen) (() => declaration seen) :=
  Parse.followsThen (followsAttributesOf Modes.start) (attributes attributesTwin attributeses =>
    followsDeclarationAttributes rule alts seen Modes.start attributes attributesTwin attributeses)

-- The facts that other lanes assume of this file's functions, each proved from the lemmas above.

theorem followsResultTypeAll ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin):
    ResultTypeFollows self selfTwin :=
  modes => followsResultType knot modes

theorem followsHeaderGroupAll ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin):
    HeaderGroupFollows self selfTwin :=
  modes kind refused => followsHeaderGroup knot modes kind refused

theorem followsBinderTypeAll ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin):
    BinderTypeFollows self selfTwin :=
  modes => followsBinderType knot modes

theorem followsPiExprAll ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin):
    PiExprFollows self selfTwin :=
  modes implicit => followsPiExpr knot modes implicit

theorem followsExpectFixedAll: ExpectFixedFollows := modes wanted what => followsExpectFixed modes wanted what

theorem followsLowerQualifiedAll: LowerQualifiedFollows := modes what => followsLowerQualified modes what

theorem attributeListAlike ∀ (attributes twins: List Attributes)
    (alike: List.All2 AttributeGroupAlike attributes twins):
    AttributesAlike attributes twins :=
  walkAttributesAlike attributes twins alike

theorem followsAttributesOfAll: AttributesOfFollows := modes =>
  Parse.followsWeaken (attributes twins alike => attributeListAlike attributes twins alike) (followsAttributesOf modes)

theorem followsDefinitionPartsAll ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin) (alts: AltPatternFollows):
    DefinitionPartsFollows self selfTwin :=
  modes local =>
    Parse.followsWeaken
      (parts twins alike => (alike.left, alike.right))
      (followsDefinitionParts knot alts modes None None None None Trivial Trivial local)
