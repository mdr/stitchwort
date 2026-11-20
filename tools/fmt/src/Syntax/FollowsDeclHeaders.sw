namespace Syntax.FollowsDeclHeaders
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
    | True => Parse.followsMap (word => Some word) (word => Some word) (followsParamName modes) (x y alike => alike)
    | False => Parse.followsDone Trivial

theorem followsParamNames ∀ (modes: Modes):
    Parse.Follows SameCode (List.All2 WordsAlike) (() => paramNames modes) (() => paramNames modes) :=
  Parse.followsLoop (followsThenEq (followsAt modes Lower) (atLower => followsParamNameStep modes atLower))

theorem followsLowerNameStep ∀ (modes: Modes) (atLower: Bool):
    Parse.Follows SameCode (Option.Alike WordsAlike) (() => lowerNameStep modes atLower) (() =>
      lowerNameStep modes atLower) :=
  match atLower with
    | True =>
      Parse.followsMap (word => Some word) (word => Some word) (followsLower modes "a name") (x y alike => alike)
    | False => Parse.followsDone Trivial

theorem followsLowerNames ∀ (modes: Modes):
    Parse.Follows SameCode (List.All2 WordsAlike) (() => lowerNames modes) (() => lowerNames modes) :=
  Parse.followsLoop (followsThenEq (followsAt modes Lower) (atLower => followsLowerNameStep modes atLower))

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
    (found twin alike => Parse.followsDone Trivial)

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
            (followsFull knot inner)
            (value valueTwin values => (colonEqs, values)))
    | False => Parse.followsDone Trivial

theorem followsConsumedBare ∀ (started startedTwin: Parse.Mark Item):
    Parse.Follows SameCode Anything (() => consumedBare started) (() => consumedBare startedTwin) :=
  Parse.followsThen Parse.followsMark (here hereTwin marks => Parse.followsDone Trivial)

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
      Parse.followsDone
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
      Parse.followsDone
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
      Parse.followsDone
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
        followsThenEq (followsAt inner ColonEq) (atEquals =>
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
    | (auto, named), (autoTwin, namedTwin) => followsThenEq (followsAt inner Colon) (atColon =>
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
        Parse.followsDone
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
        Parse.followsDone
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
        (followsLower modes "a row variable")
        (name nameTwin names => (bars, names)))
    | False => Parse.followsDone Trivial

theorem followsRowClose ∀ (modes: Modes) (open openTwin: Comments) (abilities twins: List Expr)
    (alike: List.All2 ExprsAlike abilities twins) (variable variableTwin: Option (Comments, Word))
    (variables: Option.Alike (PairAlike Anything WordsAlike) variable variableTwin):
    Parse.Follows SameCode RowsAlike (() => rowClose modes open abilities variable) (() =>
      rowClose modes openTwin twins variableTwin) :=
  Parse.followsThen (followsExpectFixed modes RBrace "`}`") (close closeTwin closes =>
    Parse.followsDone (alikeRow open openTwin abilities twins alike variable variableTwin variables close closeTwin))

theorem followsRowVariable ∀ (modes: Modes) (open openTwin: Comments) (abilities twins: List Expr)
    (alike: List.All2 ExprsAlike abilities twins):
    Parse.Follows SameCode RowsAlike (() => rowVariable modes open abilities) (() =>
      rowVariable modes openTwin twins) :=
  followsThenEq (followsAt modes Pipe) (pipe =>
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
    | True => Parse.followsDone Trivial
    | False => Parse.followsThen (knot { modes, level = LevelApp }) (first firstTwin firsts =>
      Parse.followsThen Parse.followsMark (here hereTwin marks =>
        rewrite marks.right.right then
          Parse.followsMap
            (pair => rowEntries pair)
            (pair => rowEntries pair)
            (followsCommaList modes
              (count => False)
              (count => False)
              (count => Parse.followsDone byComputing)
              (() => self { modes, level = LevelApp })
              (() => selfTwin { modes, level = LevelApp })
              (knot { modes, level = LevelApp })
              (hereTwin.left + 1)
              first
              firstTwin
              firsts
              []
              []
              Trivial)
            (pair pairTwin pairs => rowEntriesAlike pair pairTwin pairs)))

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
          followsThenEq (followsAt modes Pipe) (pipe =>
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
      (followsFull knot allowed)
      (result resultTwin results => alikeEffect row rowTwin rows result resultTwin results))

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
