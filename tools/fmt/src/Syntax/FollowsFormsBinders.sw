--| Two runs of the parser on items that differ only in their comments give alike trees (docs/reviews/
--| SW-4132-two-run-parse.md), continued from `Syntax.FollowsForms`: the binders, lambdas and quantifiers.
--| It has the facts about the other files' functions that the forms call, the statement-level facts in tiers,
--| parameters, lambdas and `∃`, `∀`, and `if`.

namespace Syntax.FollowsFormsBinders
import Std (Bool, DecEq, Eq, List, Nat, Option, Pair, Parse, Result, Text, Unit, Void)
import Syntax (..)
import Fmt (..)
import Fmt.Walk (..)
import Fmt.BlankProofs (blankPure)
import Syntax.DeafProofs (..)
import Syntax.FollowsBase (..)
import Syntax.FollowsLadder (..)
import Syntax.FollowsForms (..)

-- Facts about the functions in other files that the forms below call directly, each for every argument.

def PatternOfFollows: Prop :=
  ∀ (modes: Modes) => Parse.Follows SameCode PatternsAlike (() => patternOf modes) (() => patternOf modes)

def HeaderGroupFollows (self selfTwin: Goal → {Parse Item} Expr): Prop :=
  ∀ (modes: Modes) (kind: GroupKind) (refused: Option Text) => Parse.Follows SameCode GroupsAlike
    (() => headerGroup self modes kind refused)
    (() => headerGroup selfTwin modes kind refused)

def BinderTypeFollows (self selfTwin: Goal → {Parse Item} Expr): Prop :=
  ∀ (modes: Modes) => Parse.Follows SameCode ExprsAlike (() => binderType self modes) (() => binderType selfTwin modes)

-- The statement-level facts in tiers, in the order the expression and statement lemmas need them (see `AtomFacts` for the
-- expression ladder). Each field is the `Follows` fact its name says, for the same `self` and `selfTwin`.

--| The tier 0 of the statement facts: the knot and the header's groups and binder types.
type HeaderFacts (self selfTwin: Goal → {Parse Item} Expr) = {
  knot: SelfFollows self selfTwin,
  groups: HeaderGroupFollows self selfTwin,
  binders: BinderTypeFollows self selfTwin
}

-- Parameters.

theorem paramsBlankCons ∀ (param: Param) (rest: List Param):
    blankParams (walkParams blankPure [param, ..rest])
      = blankParams (walkParams blankPure [param]) ++ blankParams (walkParams blankPure rest) :=
  match param with | NameParam _ | PatternParam _ | Grouped _ | TypedPattern _ _ _ _ _ => byComputing

theorem paramsBlank ∀ (params twins: List Param)
    (alike: List.All2 ParamsAlike params twins):
    blankParams (walkParams blankPure params) = blankParams (walkParams blankPure twins) :=
  List.all2Join
    [f := list => blankParams (walkParams blankPure list)]
    [key := param => blankParams (walkParams blankPure [param])]
    (k rest => k ++ rest)
    paramsBlankCons
    (param twin same => same)
    params
    twins
    alike

theorem alikeNameParam ∀ (word twin: Word)
    (words: WordsAlike word twin):
    ParamsAlike (NameParam word) (NameParam twin) :=
  calc blankParams (walkParams blankPure [NameParam word])
    _ = [NameParam word.blank] := byComputing
    _ = [NameParam twin.blank] := rewrite words
    _ = blankParams (walkParams blankPure [NameParam twin]) := byComputing

theorem alikePatternParam ∀ (pattern twin: Pattern)
    (patterns: PatternsAlike pattern twin):
    ParamsAlike (PatternParam pattern) (PatternParam twin) :=
  calc blankParams (walkParams blankPure [PatternParam pattern])
    _ = [PatternParam (pattern.walk blankPure)] := byComputing
    _ = [PatternParam (twin.walk blankPure)] := rewrite patterns
    _ = blankParams (walkParams blankPure [PatternParam twin]) := byComputing

theorem alikeGrouped ∀ (group twin: Group)
    (groups: GroupsAlike group twin):
    ParamsAlike (Grouped group) (Grouped twin) :=
  calc blankParams (walkParams blankPure [Grouped group])
    _ = [Grouped (group.walk blankPure).blank] := byComputing
    _ = [Grouped (twin.walk blankPure).blank] := rewrite groups
    _ = blankParams (walkParams blankPure [Grouped twin]) := byComputing

theorem alikeTypedPattern ∀ (open openTwin: Word)
    (opens: WordsAlike open openTwin) (pattern twin: Pattern)
    (patterns: PatternsAlike pattern twin) (colon colonTwin: Word)
    (colons: WordsAlike colon colonTwin) (annotation annotationTwin: Expr)
    (annotations: ExprsAlike annotation annotationTwin) (close closeTwin: Word)
    (closes: WordsAlike close closeTwin):
    ParamsAlike
      (TypedPattern open pattern colon annotation close)
      (TypedPattern openTwin twin colonTwin annotationTwin closeTwin) :=
  calc blankParams (walkParams blankPure [TypedPattern open pattern colon annotation close])
    _ = [TypedPattern open.blank (pattern.walk blankPure) colon.blank (annotation.walk blankPure) close.blank] :=
      byComputing
    _ = [
        TypedPattern openTwin.blank
          (twin.walk blankPure)
          colonTwin.blank
          (annotationTwin.walk blankPure)
          closeTwin.blank
      ] := rewrite opens, patterns, colons, annotations, closes
    _ = blankParams (walkParams blankPure [TypedPattern openTwin twin colonTwin annotationTwin closeTwin]) :=
      byComputing

theorem keywordBlank ∀ (keyword keywordTwin: Option Word)
    (alike: Option.Alike WordsAlike keyword keywordTwin):
    keyword.map Word.blank = keywordTwin.map Word.blank :=
  match keyword, keywordTwin with
    | None, None => byComputing
    | Some word, Some twin => rewrite alike

theorem keywordIsSome ∀ (keyword keywordTwin: Option Word)
    (alike: Option.Alike WordsAlike keyword keywordTwin):
    keyword.isSome = keywordTwin.isSome :=
  match keyword, keywordTwin with
    | None, None => byComputing
    | Some word, Some twin => byComputing

theorem alikeBinding ∀ (kind: BindingKind) (keyword keywordTwin: Option Word)
    (keywords: Option.Alike WordsAlike keyword keywordTwin) (params twins: List Param)
    (alike: List.All2 ParamsAlike params twins) (arrow arrowTwin: Word)
    (arrows: WordsAlike arrow arrowTwin) (body bodyTwin: Expr)
    (bodies: ExprsAlike body bodyTwin):
    ExprsAlike (Binding kind keyword params arrow body) (Binding kind keywordTwin twins arrowTwin bodyTwin) :=
  calc (Binding kind keyword params arrow body).walk blankPure
    _ = Binding kind
        (keyword.map Word.blank)
        (blankParams (walkParams blankPure params))
        arrow.blank
        (body.walk blankPure) := byComputing
    _ = Binding kind
        (keywordTwin.map Word.blank)
        (blankParams (walkParams blankPure twins))
        arrowTwin.blank
        (bodyTwin.walk blankPure) :=
      rewrite keywordBlank keyword keywordTwin keywords, paramsBlank params twins alike, arrows, bodies
    _ = (Binding kind keywordTwin twins arrowTwin bodyTwin).walk blankPure := byComputing

-- Lambdas and `∃`.

theorem followsLambdaGroup ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (groups: HeaderGroupFollows self selfTwin) (modes: Modes):
    Parse.Follows SameCode (Option.Alike ParamsAlike) (() => lambdaGroup self modes) (() =>
      lambdaGroup selfTwin modes) :=
  Parse.followsThen (groups modes GroupLambda (Some defaultPlaces)) (group groupTwin groups =>
    Parse.followsDone (alikeGrouped group groupTwin groups))

theorem followsLambdaPattern ∀ [self selfTwin: Goal → {Parse Item} Expr] (patterns: PatternOfFollows)
    (binders: BinderTypeFollows self selfTwin)
    (modes: Modes) (typed: Bool):
    Parse.Follows SameCode (Option.Alike ParamsAlike) (() => lambdaPattern self modes typed) (() =>
      lambdaPattern selfTwin modes typed) :=
  match typed with
    | True => Parse.followsThen followsBump (open openTwin opens =>
      Parse.followsThen (patterns modes.inBrackets) (found foundTwin founds =>
        Parse.followsThen (followsExpect modes.inBrackets Colon "`:`") (colon colonTwin colons =>
          Parse.followsThen (binders modes.inBrackets) (annotation annotationTwin annotations =>
            Parse.followsThen (followsExpect modes.inBrackets RParen "`)`") (close closeTwin closes =>
              Parse.followsDone
                (alikeTypedPattern open openTwin opens found foundTwin founds colon colonTwin colons annotation
                    annotationTwin annotations close closeTwin closes))))))
    | False => Parse.followsThen (patterns modes) (found foundTwin founds =>
      Parse.followsDone (alikePatternParam found foundTwin founds))

theorem followsLambdaParen ∀ [self selfTwin: Goal → {Parse Item} Expr] (patterns: PatternOfFollows)
    (groups: HeaderGroupFollows self selfTwin)
    (binders: BinderTypeFollows self selfTwin)
    (modes: Modes) (items others: List Item)
    (same: List.All2 SameCode items others):
    Parse.Follows SameCode (Option.Alike ParamsAlike) (() => lambdaParen self modes items) (() =>
      lambdaParen selfTwin modes others) :=
  let params: annotatedParamAhead items = annotatedParamAhead others :=
    deafOfStripped annotatedParamAhead annotatedParamAheadDeaf items others same
  rewrite params then
    match annotatedParamAhead others with
      | True => followsLambdaGroup groups modes
      | False => Parse.followsThen Parse.followsMark (here hereTwin marks =>
        let typed: annotatedPatternAhead (here.left + 1) items = annotatedPatternAhead (hereTwin.left + 1) others :=
          rewrite <- marks.right.right then
            deafOfStripped
              (annotatedPatternAhead (here.left + 1))
              (annotatedPatternAheadDeaf (here.left + 1))
              items
              others
              same
        rewrite typed then
          followsLambdaPattern patterns binders modes (annotatedPatternAhead (hereTwin.left + 1) others))

theorem followsLambdaParam ∀ [self selfTwin: Goal → {Parse Item} Expr] (patterns: PatternOfFollows)
    (groups: HeaderGroupFollows self selfTwin)
    (binders: BinderTypeFollows self selfTwin)
    (modes: Modes) (items others: List Item)
    (same: List.All2 SameCode items others) (kind: Tok):
    Parse.Follows SameCode (Option.Alike ParamsAlike) (() => lambdaParam self modes items kind) (() =>
      lambdaParam selfTwin modes others kind) :=
  match kind with
    | Lower => Parse.followsThen (followsLower modes "a name") (name nameTwin names =>
      Parse.followsDone (alikeNameParam name nameTwin names))
    | Underscore =>
      Parse.followsThen followsBump (name nameTwin names => Parse.followsDone (alikeNameParam name nameTwin names))
    | LParen => followsLambdaParen patterns groups binders modes items others same
    | LBracket =>
      let implicits: implicitGroupAt items = implicitGroupAt others :=
        deafOfStripped implicitGroupAt implicitGroupAtDeaf items others same
      let autos: namelessAutoAt items = namelessAutoAt others :=
        deafOfStripped namelessAutoAt namelessAutoAtDeaf items others same
      rewrite implicits, autos then
        match implicitGroupAt others || namelessAutoAt others with
          | True => followsLambdaGroup groups modes
          | False => Parse.followsDone Trivial
    | LBrace => Parse.followsThen (patterns modes) (found foundTwin founds =>
      Parse.followsDone (alikePatternParam found foundTwin founds))
    | _ => Parse.followsDone Trivial

theorem followsLambdaStep ∀ [self selfTwin: Goal → {Parse Item} Expr] (patterns: PatternOfFollows)
    (groups: HeaderGroupFollows self selfTwin)
    (binders: BinderTypeFollows self selfTwin)
    (modes: Modes) (items others: List Item)
    (same: List.All2 SameCode items others):
    Parse.Follows SameCode (Option.Alike ParamsAlike) (() => lambdaStep self modes items) (() =>
      lambdaStep selfTwin modes others) :=
  match items, others with
    | [], [] => Parse.followsDone Trivial
    | [item, ..rest], [other, ..restTwin] =>
      let kinds: item.kind = other.kind := kindSame item other same.left
      let stops: modes.stops item = modes.stops other := stopsSame modes item other same.left
      rewrite stops, kinds then
        match modes.stops other with
          | True => Parse.followsDone Trivial
          | False => followsLambdaParam patterns groups binders modes items others same other.kind

theorem followsLambdaParams ∀ [self selfTwin: Goal → {Parse Item} Expr] (patterns: PatternOfFollows)
    (groups: HeaderGroupFollows self selfTwin)
    (binders: BinderTypeFollows self selfTwin) (modes: Modes):
    Parse.Follows SameCode (List.All2 ParamsAlike) (() => lambdaParams self modes) (() =>
      lambdaParams selfTwin modes) :=
  Parse.followsLoop
    (followsOn (seen => lambdaStep self modes seen) (seen => lambdaStep selfTwin modes seen) (seen others same =>
      followsLambdaStep patterns groups binders modes seen others same))

theorem followsBindingEnd ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (modes: Modes) (keyword keywordTwin: Option Word)
    (keywords: Option.Alike WordsAlike keyword keywordTwin) (params twins: List Param)
    (alike: List.All2 ParamsAlike params twins) (kind: BindingKind):
    Parse.Follows SameCode ExprsAlike
      (() => (let arrow := modes.expect FatArrow "`=>`"; Binding kind keyword params arrow (full self modes)))
      (() => (let arrow := modes.expect FatArrow "`=>`"; Binding kind keywordTwin twins arrow (full selfTwin modes))) :=
  Parse.followsThen (followsExpect modes FatArrow "`=>`") (arrow arrowTwin arrows =>
    Parse.followsMap
      (body => Binding kind keyword params arrow body)
      (body => Binding kind keywordTwin twins arrowTwin body)
      (followsFull knot modes)
      (body bodyTwin bodies =>
        alikeBinding kind keyword keywordTwin keywords params twins alike arrow arrowTwin arrows body bodyTwin bodies))

theorem followsLambdaKeyword ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (modes: Modes) (keyword keywordTwin: Option Word)
    (keywords: Option.Alike WordsAlike keyword keywordTwin) (params twins: List Param)
    (alike: List.All2 ParamsAlike params twins):
    Parse.Follows SameCode ExprsAlike
      (() =>
        (if params.isEmpty then modes.fail "a parameter name"
         else
           let arrow := modes.expect FatArrow "`=>`"
           Binding (if keyword.isSome then BindsExists else BindsLambda) keyword params arrow (full self modes)))
      (() =>
        (if twins.isEmpty then modes.fail "a parameter name"
         else
           let arrow := modes.expect FatArrow "`=>`"
           Binding
             (if keywordTwin.isSome then BindsExists else BindsLambda)
             keywordTwin
             twins
             arrow
             (full selfTwin modes))) :=
  match params, twins with
    | [], [] => followsFail modes "a parameter name" (() => modes.fail "a parameter name")
    | [param, ..rest], [twin, ..restTwin] =>
      rewrite keywordIsSome keyword keywordTwin keywords then
        match keywordTwin.isSome with
          | True => followsBindingEnd knot modes keyword keywordTwin keywords _ _ alike BindsExists
          | False => followsBindingEnd knot modes keyword keywordTwin keywords _ _ alike BindsLambda

theorem followsLambdaOf ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (facts: HeaderFacts self selfTwin)
    (patterns: PatternOfFollows) (modes: Modes) (keyword keywordTwin: Option Word)
    (keywords: Option.Alike WordsAlike keyword keywordTwin):
    Parse.Follows SameCode ExprsAlike (() => lambda self modes keyword) (() => lambda selfTwin modes keywordTwin) :=
  Parse.followsThen (followsLambdaParams patterns facts.groups facts.binders modes) (params twins alike =>
    followsLambdaKeyword facts.knot modes keyword keywordTwin keywords params twins alike)

theorem followsExistsLambda ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (facts: HeaderFacts self selfTwin)
    (patterns: PatternOfFollows) (modes: Modes) (keyword keywordTwin: Word)
    (keywords: WordsAlike keyword keywordTwin) (ahead: Bool):
    Parse.Follows SameCode ExprsAlike (() => existsLambda self modes keyword ahead) (() =>
      existsLambda selfTwin modes keywordTwin ahead) :=
  match ahead with
    | True => followsLambdaOf facts patterns modes (Some keyword) (Some keywordTwin) keywords
    | False =>
      followsFail modes "a parameter and `=>` after `exists`" (() => modes.fail "a parameter and `=>` after `exists`")

theorem followsExistsExpr ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (facts: HeaderFacts self selfTwin)
    (patterns: PatternOfFollows) (modes: Modes):
    Parse.Follows SameCode ExprsAlike (() => existsExpr self modes) (() => existsExpr selfTwin modes) :=
  Parse.followsThen followsBump (keyword keywordTwin keywords =>
    Parse.followsThen Parse.followsMark (here hereTwin marks =>
      rewrite <- marks.right.right then
        Parse.followsThen followsLeft (seen others same =>
          rewrite lambdaAheadSame modes (here.left + 1) seen others same then
            followsExistsLambda facts patterns modes keyword keywordTwin keywords
              (lambdaAhead modes (here.left + 1) others))))

-- `∀`.

theorem followsForallGroup ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (groups: HeaderGroupFollows self selfTwin) (modes: Modes):
    Parse.Follows SameCode (Option.Alike ParamsAlike) (() => forallGroup self modes) (() =>
      forallGroup selfTwin modes) :=
  Parse.followsThen (groups modes GroupLambda (Some forallDefault)) (group groupTwin groups =>
    Parse.followsDone (alikeGrouped group groupTwin groups))

theorem followsForallParam ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (groups: HeaderGroupFollows self selfTwin)
    (modes: Modes) (items others: List Item)
    (same: List.All2 SameCode items others) (item other: Item)
    (head: SameCode item other):
    Parse.Follows SameCode (Option.Alike ParamsAlike) (() => forallParam self modes items item) (() =>
      forallParam selfTwin modes others other) :=
  let kinds: item.kind = other.kind := kindSame item other head
  rewrite kinds then
    match other.kind with
      | Lower =>
        let qualified: isQualified item = isQualified other := deafItem isQualified isQualifiedDeaf item other head
        rewrite qualified then
          match isQualified other with
            | True => Parse.followsDone Trivial
            | False => Parse.followsThen followsBump (name nameTwin names =>
              Parse.followsDone (alikeNameParam name nameTwin names))
      | Underscore =>
        Parse.followsThen followsBump (name nameTwin names => Parse.followsDone (alikeNameParam name nameTwin names))
      | LParen =>
        let params: annotatedParamAhead items = annotatedParamAhead others :=
          deafOfStripped annotatedParamAhead annotatedParamAheadDeaf items others same
        rewrite params then
          match annotatedParamAhead others with
            | True => followsForallGroup groups modes
            | False => Parse.followsDone Trivial
      | LBracket =>
        let implicits: implicitGroupAt items = implicitGroupAt others :=
          deafOfStripped implicitGroupAt implicitGroupAtDeaf items others same
        let autos: namelessAutoAt items = namelessAutoAt others :=
          deafOfStripped namelessAutoAt namelessAutoAtDeaf items others same
        rewrite implicits, autos then
          match implicitGroupAt others || namelessAutoAt others with
            | True => followsForallGroup groups modes
            | False => Parse.followsDone Trivial
      | _ => Parse.followsDone Trivial

theorem followsForallStep ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (groups: HeaderGroupFollows self selfTwin)
    (modes: Modes) (items others: List Item)
    (same: List.All2 SameCode items others):
    Parse.Follows SameCode (Option.Alike ParamsAlike) (() => forallStep self modes items) (() =>
      forallStep selfTwin modes others) :=
  match items, others with
    | [], [] => Parse.followsDone Trivial
    | [item, ..rest], [other, ..restTwin] =>
      let stops: modes.stops item = modes.stops other := stopsSame modes item other same.left
      rewrite stops then
        match modes.stops other with
          | True => Parse.followsDone Trivial
          | False => followsForallParam groups modes items others same item other same.left

theorem followsForallParams ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (groups: HeaderGroupFollows self selfTwin) (modes: Modes):
    Parse.Follows SameCode (List.All2 ParamsAlike) (() => forallParams self modes) (() =>
      forallParams selfTwin modes) :=
  Parse.followsLoop
    (followsOn (seen => forallStep self modes seen) (seen => forallStep selfTwin modes seen) (seen others same =>
      followsForallStep groups modes seen others same))

theorem followsForallArrow ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (modes: Modes) (keyword keywordTwin: Word)
    (keywords: WordsAlike keyword keywordTwin) (params twins: List Param)
    (alike: List.All2 ParamsAlike params twins) (atArrow: Bool):
    Parse.Follows SameCode ExprsAlike (() => forallArrow self modes keyword params atArrow) (() =>
      forallArrow selfTwin modes keywordTwin twins atArrow) :=
  match atArrow with
    | True => Parse.followsThen followsBump (arrow arrowTwin arrows =>
      Parse.followsMap
        (body => Binding BindsForall (Some keyword) params arrow body)
        (body => Binding BindsForall (Some keywordTwin) twins arrowTwin body)
        (followsFull knot modes)
        (body bodyTwin bodies =>
          alikeBinding BindsForall
            (Some keyword)
            (Some keywordTwin)
            keywords
            params
            twins
            alike
            arrow
            arrowTwin
            arrows
            body
            bodyTwin
            bodies))
    | False => followsFail modes "`=>` after the parameters of `${keyword.text}`" (() =>
      modes.fail "`=>` after the parameters of `${keywordTwin.text}`")

theorem followsForallExpr ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (groups: HeaderGroupFollows self selfTwin) (modes: Modes):
    Parse.Follows SameCode ExprsAlike (() => forallExpr self modes) (() => forallExpr selfTwin modes) :=
  Parse.followsThen followsBump (keyword keywordTwin keywords =>
    Parse.followsThen (followsForallParams groups modes) (params twins alike =>
      match params, twins with
        | [], [] => followsFail modes "a parameter after `${keyword.text}`" (() =>
          modes.fail "a parameter after `${keywordTwin.text}`")
        | [param, ..rest], [twin, ..restTwin] => followsThenEq (followsAt modes FatArrow) (atArrow =>
          followsForallArrow knot modes keyword keywordTwin keywords _ _ alike atArrow)))

-- Quantifiers: `∃` and `∀`.

theorem followsQuantifierOn ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (facts: HeaderFacts self selfTwin)
    (patterns: PatternOfFollows) (modes: Modes) (items others: List Item)
    (same: List.All2 SameCode items others):
    Parse.Follows SameCode ExprsAlike (() => quantifierOn self modes items) (() =>
      quantifierOn selfTwin modes others) :=
  match items, others with
    | [], [] => followsExistsExpr facts patterns modes
    | [item, ..rest], [other, ..restTwin] =>
      rewrite kindSame item other same.left then
        match other.kind == KwForall with
          | True => followsForallExpr facts.knot facts.groups modes
          | False => followsExistsExpr facts patterns modes

theorem followsQuantifier ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (facts: HeaderFacts self selfTwin)
    (patterns: PatternOfFollows) (modes: Modes):
    Parse.Follows SameCode ExprsAlike (() => Syntax.quantifier self modes) (() => Syntax.quantifier selfTwin modes) :=
  byWalking [followsQuantifierOn]

-- `if`.

theorem lineStartSame ∀ (item other: Item)
    (same: SameCode item other):
    item.leaf.token.lineStart = other.leaf.token.lineStart :=
  deafItem (found => found.leaf.token.lineStart) (found => byComputing) item other same

theorem columnSame ∀ (item other: Item) (same: SameCode item other): item.leaf.token.column = other.leaf.token.column :=
  deafItem (found => found.leaf.token.column) (found => byComputing) item other same

theorem followsExpectKeywordOn ∀ (modes: Modes) (wanted: Tok) (what: Text) (indent: Nat)
    (seen: Option Tok) (items others: List Item)
    (same: List.All2 SameCode items others):
    Parse.Follows SameCode WordsAlike (() => modes.expectKeywordOn wanted what indent seen items) (() =>
      modes.expectKeywordOn wanted what indent seen others) :=
  match seen with
    | None =>
      match items, others with
        | [], [] => followsExpect modes wanted what
        | [item, ..rest], [other, ..restTwin] =>
          let kinds: item.kind = other.kind := kindSame item other same.left
          let starts: item.leaf.token.lineStart = other.leaf.token.lineStart := lineStartSame item other same.left
          let columns: item.leaf.token.column = other.leaf.token.column := columnSame item other same.left
          let guards: (item.kind == wanted && item.leaf.token.lineStart && item.leaf.token.column >= indent)
            = (other.kind == wanted && other.leaf.token.lineStart && other.leaf.token.column >= indent) :=
            rewrite kinds, starts, columns
          match chosen: item.kind == wanted
            && item.leaf.token.lineStart
            && item.leaf.token.column >= indent, chosenTwin: other.kind == wanted
            && other.leaf.token.lineStart
            && other.leaf.token.column >= indent with
            | True, True => followsBump
            | False, False => followsExpect modes wanted what
    | Some kind => followsExpect modes wanted what

theorem followsExpectKeyword ∀ (modes: Modes) (wanted: Tok) (what: Text) (indent: Nat):
    Parse.Follows SameCode WordsAlike (() => modes.expectKeyword wanted what indent) (() =>
      modes.expectKeyword wanted what indent) :=
  byWalking [followsExpectKeywordOn]

theorem followsNamedBinderOn ∀ (modes: Modes) (lower: Bool) (second: Option Tok):
    Parse.Follows SameCode
      (Option.Alike (PairAlike WordsAlike WordsAlike))
      (() => namedBinderOn modes lower second)
      (() => namedBinderOn modes lower second) :=
  byWalking [followsLower]

theorem followsNamedBinder ∀ (modes: Modes):
    Parse.Follows SameCode (Option.Alike (PairAlike WordsAlike WordsAlike)) (() => namedBinder modes) (() =>
      namedBinder modes) :=
  byWalking [followsNamedBinderOn]

theorem pairBlank ∀ (binder binderTwin: Option (Word, Word))
    (alike: Option.Alike (PairAlike WordsAlike WordsAlike) binder binderTwin):
    blankPair binder = blankPair binderTwin :=
  match binder, binderTwin with
    | None, None => byComputing
    | Some (first, second), Some (firstTwin, secondTwin) =>
      calc blankPair (Some (first, second))
        _ = Some (first.blank, second.blank) := byComputing
        _ = Some (firstTwin.blank, secondTwin.blank) := rewrite alike.left, alike.right
        _ = blankPair (Some (firstTwin, secondTwin)) := byComputing

theorem alikeIf ∀ (keyword keywordTwin: Word)
    (keywords: WordsAlike keyword keywordTwin) (binder binderTwin: Option (Word, Word))
    (binders: Option.Alike (PairAlike WordsAlike WordsAlike) binder binderTwin) (condition conditionTwin: Expr)
    (conditions: ExprsAlike condition conditionTwin) (thenKeyword thenKeywordTwin: Word)
    (thens: WordsAlike thenKeyword thenKeywordTwin) (whenTrue whenTrueTwin: Expr)
    (trues: ExprsAlike whenTrue whenTrueTwin) (elseKeyword elseKeywordTwin: Word)
    (elses: WordsAlike elseKeyword elseKeywordTwin) (whenFalse whenFalseTwin: Expr)
    (falses: ExprsAlike whenFalse whenFalseTwin):
    ExprsAlike
      (If keyword binder condition thenKeyword whenTrue elseKeyword whenFalse)
      (If keywordTwin binderTwin conditionTwin thenKeywordTwin whenTrueTwin elseKeywordTwin whenFalseTwin) :=
  calc (If keyword binder condition thenKeyword whenTrue elseKeyword whenFalse).walk blankPure
    _ = If keyword.blank
        (blankPair binder)
        (condition.walk blankPure)
        thenKeyword.blank
        (whenTrue.walk blankPure)
        elseKeyword.blank
        (whenFalse.walk blankPure) := byComputing
    _ = If keywordTwin.blank
        (blankPair binderTwin)
        (conditionTwin.walk blankPure)
        thenKeywordTwin.blank
        (whenTrueTwin.walk blankPure)
        elseKeywordTwin.blank
        (whenFalseTwin.walk blankPure) :=
      rewrite keywords, pairBlank binder binderTwin binders, conditions, thens, trues, elses, falses
    _ = (If keywordTwin binderTwin conditionTwin thenKeywordTwin whenTrueTwin elseKeywordTwin whenFalseTwin).walk
          blankPure := byComputing

theorem followsIfExpr ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (modes: Modes) (indent: Nat) (keyword keywordTwin: Word)
    (keywords: WordsAlike keyword keywordTwin):
    Parse.Follows SameCode ExprsAlike (() => ifExpr self modes indent keyword) (() =>
      ifExpr selfTwin modes indent keywordTwin) :=
  Parse.followsThen (followsNamedBinder modes) (binder binderTwin binders =>
    Parse.followsThen (followsFull knot modes.sealed) (condition conditionTwin conditions =>
      Parse.followsThen (followsExpectKeyword modes KwThen "`then`" indent) (thenKeyword thenKeywordTwin thens =>
        Parse.followsThen (followsFull knot modes.sealed) (whenTrue whenTrueTwin trues =>
          Parse.followsThen (followsExpectKeyword modes KwElse "`else`" indent) (elseKeyword elseKeywordTwin elses =>
            Parse.followsMap
              (whenFalse => If keyword binder condition thenKeyword whenTrue elseKeyword whenFalse)
              (whenFalse =>
                If keywordTwin binderTwin conditionTwin thenKeywordTwin whenTrueTwin elseKeywordTwin whenFalse)
              (followsFull knot modes)
              (whenFalse whenFalseTwin falses =>
                alikeIf keyword keywordTwin keywords binder binderTwin binders condition conditionTwin conditions
                    thenKeyword thenKeywordTwin thens whenTrue whenTrueTwin trues elseKeyword elseKeywordTwin elses
                    whenFalse whenFalseTwin falses))))))
