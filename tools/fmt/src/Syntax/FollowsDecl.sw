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

-- Reading a fixed token: its comments are not compared.

theorem followsExpectFixed ∀ (modes: Modes) (wanted: Tok) (what: Text):
    Parse.Follows SameCode Anything (() => modes.expectFixed wanted what) (() => modes.expectFixed wanted what) :=
  Parse.followsThen (followsExpect modes wanted what) (found twin alike =>
    Parse.followsDone found.comments twin.comments Trivial)

-- A step that reads the number of items left to make fuel.

theorem followsFuel ∀ [alike: a → b → Prop] (k: Nat → {Parse Item} a) (kTwin: Nat → {Parse Item} b)
    (each: ∀ (fuel: Nat) => Parse.Follows SameCode alike (() => k fuel) (() => kTwin fuel)):
    Parse.Follows SameCode alike (() => k (Parse.mark().left + 1)) (() => kTwin (Parse.mark().left + 1)) :=
  Parse.followsThen
    [p := () => Parse.mark()]
    [q := () => Parse.mark()]
    [j := here => k (here.left + 1)]
    [k := here => kTwin (here.left + 1)]
    Parse.followsMark
    (here hereTwin marks => rewrite marks.right.right then each (hereTwin.left + 1))

-- Relations.

def attributeBlank (attribute: Attribute): Attribute :=
  { name = attribute.name.blank, parts = blankDottedParts attribute.parts, argument = attribute.argument.map Word.blank }

def AttributeAlike (attribute twin: Attribute): Prop := attributeBlank attribute = attributeBlank twin

def AttributesAlike (attributes twin: Attributes): Prop := blankAttributes attributes = blankAttributes twin

theorem optionWordBlank ∀ (word twin: Option Word) (alike: Option.Alike WordsAlike word twin):
    word.map Word.blank = twin.map Word.blank :=
  match word, twin with
    | Some x, Some y => Eq.cong (found => Some found) alike
    | None, None => byComputing

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

theorem alikeAttribute ∀ (name nameTwin: Word) (names: WordsAlike name nameTwin)
    (parts partsTwin: List (Comments, Word)) (partses: List.All2 (PairAlike Anything WordsAlike) parts partsTwin)
    (argument argumentTwin: Option Word) (arguments: Option.Alike WordsAlike argument argumentTwin):
    AttributeAlike { name, parts, argument } { name = nameTwin, parts = partsTwin, argument = argumentTwin } :=
  calc attributeBlank { name, parts, argument }
    _ = { name = name.blank, parts = blankDottedParts parts, argument = argument.map Word.blank } := byComputing
    _ = { name = nameTwin.blank, parts = blankDottedParts partsTwin, argument = argumentTwin.map Word.blank } :=
      rewrite names, dottedAlike parts partsTwin partses, optionWordBlank argument argumentTwin arguments
    _ = attributeBlank { name = nameTwin, parts = partsTwin, argument = argumentTwin } := byComputing

theorem attributeItemsCons ∀ (item: Attribute) (rest: List Attribute):
    blankAttributeItems [item, ..rest] = [attributeBlank item, ..blankAttributeItems rest] :=
  match item with | { name, parts, argument } => byComputing

theorem attributeItemsAlike ∀ (items twins: List Attribute) (alike: List.All2 AttributeAlike items twins):
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
    (alike: List.All2 AttributeAlike items twins) (trailing trailingTwin: Bool) (trailings: trailing = trailingTwin)
    (close closeTwin: Comments):
    AttributesAlike { at, open, items, trailingComma = trailing, close }
      { at = atTwin, open = openTwin, items = twins, trailingComma = trailingTwin, close = closeTwin } :=
  calc blankAttributes { at, open, items, trailingComma = trailing, close }
    _ = { at = Comments.none,
          open = Comments.none,
          items = blankAttributeItems items,
          trailingComma = trailing,
          close = Comments.none } := byComputing
    _ = { at = Comments.none,
          open = Comments.none,
          items = blankAttributeItems twins,
          trailingComma = trailingTwin,
          close = Comments.none } := rewrite attributeItemsAlike items twins alike, trailings
    _ = blankAttributes { at = atTwin, open = openTwin, items = twins, trailingComma = trailingTwin, close = closeTwin } :=
      byComputing

theorem walkAttributesAlike ∀ (items twins: List Attributes) (alike: List.All2 AttributesAlike items twins):
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

theorem all2Empty ∀ [r: a → b → Prop] (xs: List a) (ys: List b) (alike: List.All2 r xs ys): xs.isEmpty = ys.isEmpty :=
  match xs, ys with
    | [], [] => byComputing
    | [x, ..xs], [y, ..ys] => byComputing

theorem wordText ∀ (word twin: Word) (alike: WordsAlike word twin): word.text = twin.text :=
  Eq.cong (found => found.text) alike

theorem followsLowerQualifiedOn ∀ (modes: Modes) (what: Text) (seen: Option Tok):
    Parse.Follows SameCode WordsAlike (() => modes.lowerQualifiedOn what seen) (() => modes.lowerQualifiedOn what seen) :=
  match isSome Lower seen with
    | True => followsBump
    | False => followsFailName modes what (() => modes.failName what)

theorem followsLowerQualified ∀ (modes: Modes) (what: Text):
    Parse.Follows SameCode WordsAlike (() => modes.lowerQualified what) (() => modes.lowerQualified what) :=
  followsPeeked modes (seen => modes.lowerQualifiedOn what seen) (seen => modes.lowerQualifiedOn what seen) (seen =>
    followsLowerQualifiedOn modes what seen)

theorem followsUpperQualifiedOn ∀ (modes: Modes) (what: Text) (seen: Option Tok):
    Parse.Follows SameCode WordsAlike (() => modes.upperQualifiedOn what seen) (() => modes.upperQualifiedOn what seen) :=
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
    rewrite wordText name nameTwin names then
      match nameTwin.text.contains "." with
        | True => followsFatalAny _ _
        | False => Parse.followsDone name nameTwin names)

theorem followsRefuseAttributes ∀ (attributes twins: List Attributes) (alike: List.All2 AttributesAlike attributes twins)
    (what: Text):
    Parse.Follows SameCode Anything (() => refuseAttributes attributes what) (() => refuseAttributes twins what) :=
  match attributes, twins with
    | [], [] => Parse.followsDone () () Trivial
    | [x, ..xs], [y, ..ys] => followsFatalAny _ _

theorem followsAttributeArgumentOn ∀ (modes: Modes) (seen: Option Tok):
    Parse.Follows SameCode (Option.Alike WordsAlike) (() => attributeArgumentOn modes seen) (() =>
      attributeArgumentOn modes seen) :=
  match isSome Str seen with
    | True => Parse.followsMap [alike := Option.Alike WordsAlike] [p := () => bump()] [q := () => bump()] (word => Some word) (word => Some word) (x y alike => alike) followsBump
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
    | True =>
      Parse.followsThen followsFixedFrom (written writtenTwin writtens =>
        Parse.followsMap
          (part => Some (written, part))
          (part => Some (writtenTwin, part))
          (part partTwin parts => (writtens, parts))
          (followsLowerQualified modes "the rest of the attribute's name"))
    | False => Parse.followsDone None None Trivial

theorem followsAttributeParts ∀ (modes: Modes):
    Parse.Follows SameCode (List.All2 (PairAlike Anything WordsAlike)) (() => attributeParts modes) (() =>
      attributeParts modes) :=
  Parse.followsLoop _ _
    (followsThenEq
      [j := dot => attributePart modes dot]
      [k := dot => attributePart modes dot]
      (followsAt modes Dot)
      (dot => followsAttributePart modes dot))

def AttributeItemsFollow (modes: Modes) (fuel: Nat): Prop :=
  ∀ (found twin: List Attribute) => List.All2 AttributeAlike found twin
    → Parse.Follows SameCode (PairAlike (List.All2 AttributeAlike) Same)
      (() => attributeItems fuel modes found)
      (() => attributeItems fuel modes twin)

theorem followsAttributeNext ∀ (more: Nat) (modes: Modes) (again: AttributeItemsFollow modes more)
    (done twins: List Attribute) (dones: List.All2 AttributeAlike done twins) (comma: Bool):
    Parse.Follows SameCode (PairAlike (List.All2 AttributeAlike) Same)
      (() => attributeNext more modes done comma)
      (() => attributeNext more modes twins comma) :=
  match comma with
    | True => Parse.followsThen followsBump (found twin alike => again done twins dones)
    | False =>
      Parse.followsDone _ _ (List.all2Reverse done twins dones, byComputing)

theorem followsAttributeItem ∀ (more: Nat) (modes: Modes) (again: AttributeItemsFollow modes more)
    (found twins: List Attribute) (founds: List.All2 AttributeAlike found twins):
    Parse.Follows SameCode (PairAlike (List.All2 AttributeAlike) Same)
      (() => attributeItem more modes found)
      (() => attributeItem more modes twins) :=
  Parse.followsThen (followsLowerQualified modes "an attribute's name, such as `js.name`") (name nameTwin names =>
    Parse.followsThen (followsAttributeParts modes) (parts partsTwin partses =>
      Parse.followsThen (followsAttributeArgument modes) (value valueTwin values =>
        followsThenEq (followsAt modes Comma) (comma =>
          followsAttributeNext more modes again
            [{ name, parts, argument = value }, ..found]
            [{ name = nameTwin, parts = partsTwin, argument = valueTwin }, ..twins]
            (Both (alikeAttribute name nameTwin names parts partsTwin partses value valueTwin values) founds)
            comma))))

theorem followsAttributeItemsAt ∀ (more: Nat) (modes: Modes) (again: AttributeItemsFollow modes more)
    (found twins: List Attribute) (founds: List.All2 AttributeAlike found twins) (closed: Bool):
    Parse.Follows SameCode (PairAlike (List.All2 AttributeAlike) Same)
      (() => attributeItemsAt more modes found closed)
      (() => attributeItemsAt more modes twins closed) :=
  let empties: found.isEmpty = twins.isEmpty := all2Empty found twins founds
  rewrite empties then
    match closed && !twins.isEmpty with
      | True =>
        Parse.followsDone (found.reverse, True) (twins.reverse, True) (List.all2Reverse found twins founds, byComputing)
      | False => followsAttributeItem more modes again found twins founds

theorem followsAttributeItems ∀ (fuel: Nat) (modes: Modes) (found twins: List Attribute)
    (founds: List.All2 AttributeAlike found twins):
    Parse.Follows SameCode (PairAlike (List.All2 AttributeAlike) Same)
      (() => attributeItems fuel modes found)
      (() => attributeItems fuel modes twins) :=
  match fuel with
    | Succ more =>
      followsThenEq (followsAt modes RBracket) (closed =>
        followsAttributeItemsAt more modes
          (again twin dones => followsAttributeItems more modes again twin dones)
          found
          twins
          founds
          closed)
    | Zero => Parse.followsDone _ _ (List.all2Reverse found twins founds, byComputing)

theorem followsAttributeGroupEnd ∀ (modes: Modes) (at atTwin open openTwin: Comments)
    (pair pairTwin: (List Attribute, Bool)) (pairs: PairAlike (List.All2 AttributeAlike) Same pair pairTwin):
    Parse.Follows SameCode (Option.Alike AttributesAlike)
      (() => attributeGroupEnd modes at open pair)
      (() => attributeGroupEnd modes atTwin openTwin pairTwin) :=
  match pair, pairTwin with
    | (items, trailing), (itemsTwin, trailingTwin) =>
      Parse.followsMap
        [alike := Option.Alike AttributesAlike]
        [p := () => modes.expectFixed RBracket "`,` or `]` after the attribute"]
        [q := () => modes.expectFixed RBracket "`,` or `]` after the attribute"]
        (close => Some { at, open, items, trailingComma = trailing, close })
        (close => Some { at = atTwin, open = openTwin, items = itemsTwin, trailingComma = trailingTwin, close })
        (close closeTwin closes =>
          alikeAttributes at atTwin open openTwin items itemsTwin pairs.left trailing trailingTwin pairs.right close
              closeTwin)
        (followsExpectFixed modes RBracket "`,` or `]` after the attribute")

theorem followsAttributeGroup ∀ (modes: Modes):
    Parse.Follows SameCode (Option.Alike AttributesAlike) (() => attributeGroup modes) (() => attributeGroup modes) :=
  Parse.followsThen followsFixedFrom (at atTwin ats =>
    Parse.followsThen (followsExpectFixed modes LBracket "`[`") (open openTwin opens =>
      Parse.followsThen
        [p := () => Parse.mark()]
        [q := () => Parse.mark()]
        [j := here => attributeGroupEnd modes at open (attributeItems (here.left + 1) modes [])]
        [k := here => attributeGroupEnd modes atTwin openTwin (attributeItems (here.left + 1) modes [])]
        Parse.followsMark
        (here hereTwin marks =>
          rewrite marks.right.right then
            Parse.followsThen
              (followsAttributeItems (hereTwin.left + 1) modes [] [] Trivial)
              (pair pairTwin pairs => followsAttributeGroupEnd modes at atTwin open openTwin pair pairTwin pairs))))

theorem followsAttributeGroupAt ∀ (modes: Modes) (found: Bool):
    Parse.Follows SameCode (Option.Alike AttributesAlike) (() => attributeGroupAt modes found) (() =>
      attributeGroupAt modes found) :=
  match found with
    | True => followsAttributeGroup modes
    | False => Parse.followsDone None None Trivial

theorem followsAttributeGroupStep ∀ (modes: Modes):
    Parse.Follows SameCode (Option.Alike AttributesAlike) (() => attributeGroupStep modes) (() =>
      attributeGroupStep modes) :=
  followsThenEq
    [j := found => attributeGroupAt modes found]
    [k := found => attributeGroupAt modes found]
    (followsAt modes At)
    (found => followsAttributeGroupAt modes found)

theorem followsAttributeGroups ∀ (modes: Modes):
    Parse.Follows SameCode (List.All2 AttributesAlike) (() => attributeGroups modes) (() => attributeGroups modes) :=
  Parse.followsLoop _ _ (followsAttributeGroupStep modes)

theorem followsAttributesOf ∀ (modes: Modes):
    Parse.Follows SameCode (List.All2 AttributesAlike) (() => attributesOf modes) (() => attributesOf modes) :=
  followsAttributeGroups modes

-- Groups.

theorem wordsBlankAlike ∀ (words twins: List Word) (alike: List.All2 WordsAlike words twins):
    blankWords words = blankWords twins :=
  match words, twins with
    | [], [] => byComputing
    | [x, ..xs], [y, ..ys] =>
      let (head, tail) := alike
      calc blankWords [x, ..xs]
        _ = [x.blank, ..blankWords xs] := byComputing
        _ = [y.blank, ..blankWords ys] := rewrite head, wordsBlankAlike xs ys tail
        _ = blankWords [y, ..ys] := byComputing

theorem commentsBlankAlike ∀ (found twin: Option Comments) (alike: Option.Alike Anything found twin):
    blankComments found = blankComments twin :=
  match found, twin with
    | Some x, Some y => byComputing
    | None, None => byComputing

theorem walkOptionalAlike ∀ (found twin: Option Expr) (alike: Option.Alike ExprsAlike found twin):
    walkOptional blankPure found = walkOptional blankPure twin :=
  match found, twin with
    | Some x, Some y => Eq.cong (value => Some value) alike
    | None, None => byComputing

theorem afterAlike ∀ (found twin: Option (Comments, Expr)) (alike: Option.Alike (PairAlike Anything ExprsAlike) found twin):
    blankAfter (walkAfter blankPure found) = blankAfter (walkAfter blankPure twin) :=
  match found, twin with
    | Some (c, x), Some (d, y) =>
      let same: x.walk blankPure = y.walk blankPure := alike.right
      calc blankAfter (walkAfter blankPure (Some (c, x)))
        _ = Some (Comments.none, x.walk blankPure) := byComputing
        _ = Some (Comments.none, y.walk blankPure) := rewrite same
        _ = blankAfter (walkAfter blankPure (Some (d, y))) := byComputing
    | None, None => byComputing

theorem alikeGroup ∀ (kind: GroupKind) (implicit: Bool) (open openTwin: Comments)
    (attributes twinAttributes: List Attributes) (attributeses: List.All2 AttributesAlike attributes twinAttributes)
    (auto autoTwin: Option Comments) (autos: Option.Alike Anything auto autoTwin)
    (names twinNames: List Word) (nameses: List.All2 WordsAlike names twinNames)
    (colon colonTwin: Option Comments) (colons: Option.Alike Anything colon colonTwin)
    (annotation annotationTwin: Option Expr) (annotations: Option.Alike ExprsAlike annotation annotationTwin)
    (default defaultTwin: Option (Comments, Expr))
    (defaults: Option.Alike (PairAlike Anything ExprsAlike) default defaultTwin)
    (close closeTwin: Comments) (bare bareTwin: Bool):
    GroupsAlike
      { kind, implicit, open, attributes, auto, names, colon, annotation, default, close, bare }
      { kind,
        implicit,
        open = openTwin,
        attributes = twinAttributes,
        auto = autoTwin,
        names = twinNames,
        colon = colonTwin,
        annotation = annotationTwin,
        default = defaultTwin,
        close = closeTwin,
        bare = bareTwin } :=
  calc ({ kind, implicit, open, attributes, auto, names, colon, annotation, default, close, bare }: Group).walk
      blankPure |>
    .blank
    _ = { kind,
          implicit,
          open = Comments.none,
          attributes = walkAttributes blankPure attributes,
          auto = blankComments auto,
          names = blankWords names,
          colon = blankComments colon,
          annotation = walkOptional blankPure annotation,
          default = blankAfter (walkAfter blankPure default),
          close = Comments.none,
          bare = True } := byComputing
    _ = { kind,
          implicit,
          open = Comments.none,
          attributes = walkAttributes blankPure twinAttributes,
          auto = blankComments autoTwin,
          names = blankWords twinNames,
          colon = blankComments colonTwin,
          annotation = walkOptional blankPure annotationTwin,
          default = blankAfter (walkAfter blankPure defaultTwin),
          close = Comments.none,
          bare = True } :=
      rewrite walkAttributesAlike attributes twinAttributes attributeses,
        commentsBlankAlike auto autoTwin autos,
        wordsBlankAlike names twinNames nameses,
        commentsBlankAlike colon colonTwin colons,
        walkOptionalAlike annotation annotationTwin annotations,
        afterAlike default defaultTwin defaults
    _ = ({ kind,
           implicit,
           open = openTwin,
           attributes = twinAttributes,
           auto = autoTwin,
           names = twinNames,
           colon = colonTwin,
           annotation = annotationTwin,
           default = defaultTwin,
           close = closeTwin,
           bare = bareTwin }: Group).walk blankPure |>
      .blank := byComputing

-- Parameter names.

theorem followsParamNameOn ∀ (modes: Modes) (seen: Option Tok):
    Parse.Follows SameCode WordsAlike (() => paramNameOn modes seen) (() => paramNameOn modes seen) :=
  match seen with
    | Some Upper => followsFail modes "a parameter's name" (() => modes.fail "a parameter's name")
    | Some LParen => followsFail modes "a parameter's name" (() => modes.fail "a parameter's name")
    | Some LBrace => followsFail modes "a parameter's name" (() => modes.fail "a parameter's name")
    | _ => followsLower modes "a parameter's name"

theorem followsParamName ∀ (modes: Modes):
    Parse.Follows SameCode WordsAlike (() => paramName modes) (() => paramName modes) :=
  followsPeeked modes (seen => paramNameOn modes seen) (seen => paramNameOn modes seen) (seen =>
    followsParamNameOn modes seen)

theorem followsParamNameStep ∀ (modes: Modes) (atLower: Bool):
    Parse.Follows SameCode (Option.Alike WordsAlike) (() => paramNameStep modes atLower) (() =>
      paramNameStep modes atLower) :=
  match atLower with
    | True => Parse.followsMap
      [alike := Option.Alike WordsAlike]
      [p := () => paramName modes]
      [q := () => paramName modes]
      (word => Some word)
      (word => Some word)
      (x y alike => alike)
      (followsParamName modes)
    | False => Parse.followsDone None None Trivial

theorem followsParamNames ∀ (modes: Modes):
    Parse.Follows SameCode (List.All2 WordsAlike) (() => paramNames modes) (() => paramNames modes) :=
  Parse.followsLoop _ _
    (followsThenEq
      [j := atLower => paramNameStep modes atLower]
      [k := atLower => paramNameStep modes atLower]
      (followsAt modes Lower)
      (atLower => followsParamNameStep modes atLower))

theorem followsLowerNameStep ∀ (modes: Modes) (atLower: Bool):
    Parse.Follows SameCode (Option.Alike WordsAlike) (() => lowerNameStep modes atLower) (() =>
      lowerNameStep modes atLower) :=
  match atLower with
    | True => Parse.followsMap
      [alike := Option.Alike WordsAlike]
      [p := () => modes.lower "a name"]
      [q := () => modes.lower "a name"]
      (word => Some word)
      (word => Some word)
      (x y alike => alike)
      (followsLower modes "a name")
    | False => Parse.followsDone None None Trivial

theorem followsLowerNames ∀ (modes: Modes):
    Parse.Follows SameCode (List.All2 WordsAlike) (() => lowerNames modes) (() => lowerNames modes) :=
  Parse.followsLoop _ _
    (followsThenEq
      [j := atLower => lowerNameStep modes atLower]
      [k := atLower => lowerNameStep modes atLower]
      (followsAt modes Lower)
      (atLower => followsLowerNameStep modes atLower))

-- A binder's type.

def skipsToType (items: List Item): Bool := match skipGroup [] items with
  | Some [next, .._] => typeStarts next.kind
  | _ => False

def binderTypeBrace (self: Goal → {Parse Item} Expr) (allowed: Modes) (flag: Bool): {Parse Item} Expr :=
  if flag then Syntax.fatal "an ability row can't be written in a parameter's type" else full self allowed

theorem skipsToTypeDeaf ∀ (items: List Item): skipsToType items = skipsToType (items.map Item.stripped) :=
  rewrite skipGroupDeaf [] items then
    match skipGroup [] items with
      | None => byComputing
      | Some [] => byComputing
      | Some [next, ..more] => byComputing

theorem binderTypeBraceEq ∀ (self: Goal → {Parse Item} Expr) (allowed: Modes) (open: Item) (rest: List Item):
    binderTypeOn self allowed (Some LBrace) [open, ..rest]
      = binderTypeBrace self allowed (skipsToType [open, ..rest]) :=
  match skipGroup [] [open, ..rest] with
    | None => byComputing
    | Some [] => byComputing
    | Some [next, ..more] =>
      match typeStarts next.kind with
        | True => byComputing
        | False => byComputing

theorem followsAllowBrace ∀ (modes: Modes):
    Parse.Follows SameCode Same (() => allowBrace modes) (() => allowBrace modes) :=
  followsLook (allowBraceOn modes) (allowBraceOnDeaf modes)

theorem followsBinderTypeOn ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin) (allowed: Modes) (seen: Option Tok) (items others: List Item)
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
    (knot: SelfFollows self selfTwin) (allowed: Modes) (seen: Option Tok):
    Parse.Follows SameCode ExprsAlike (() => binderTypeSeen self allowed seen) (() =>
      binderTypeSeen selfTwin allowed seen) :=
  followsOn
    (items => binderTypeOn self allowed seen items)
    (items => binderTypeOn selfTwin allowed seen items)
    (items others same => followsBinderTypeOn knot allowed seen items others same)

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
    (knot: SelfFollows self selfTwin) (inner: Modes) (implicit atColonEq: Bool):
    Parse.Follows SameCode (Option.Alike (PairAlike Anything ExprsAlike))
      (() => headerDefault self inner implicit atColonEq)
      (() => headerDefault selfTwin inner implicit atColonEq) :=
  match atColonEq with
    | True =>
      match implicit with
        | True => followsFatalAny _ _
        | False =>
          Parse.followsThen followsFixedFrom (colonEq colonEqTwin colonEqs =>
            Parse.followsMap
              [alike := Option.Alike (PairAlike Anything ExprsAlike)]
              [p := () => full self inner]
              [q := () => full selfTwin inner]
              (value => Some (colonEq, value))
              (value => Some (colonEqTwin, value))
              (value valueTwin values => (colonEqs, values))
              (followsFull knot inner))
    | False => Parse.followsDone None None Trivial

theorem followsConsumedBare ∀ (started startedTwin: Parse.Mark Item):
    Parse.Follows SameCode Anything (() => consumedBare started) (() => consumedBare startedTwin) :=
  Parse.followsThen Parse.followsMark (here hereTwin marks => Parse.followsDone _ _ Trivial)

theorem followsHeaderGroupEnd ∀ (kind: GroupKind) (implicit: Bool) (open openTwin: Comments) (auto autoTwin: Option Comments)
    (autos: Option.Alike Anything auto autoTwin) (named namedTwin: List Word)
    (nameds: List.All2 WordsAlike named namedTwin) (colon colonTwin: Comments) (annotation annotationTwin: Expr)
    (annotations: ExprsAlike annotation annotationTwin) (default defaultTwin: Option (Comments, Expr))
    (defaults: Option.Alike (PairAlike Anything ExprsAlike) default defaultTwin) (close closeTwin: Comments)
    (refused: Option Text) (consumed consumedTwin: Bool):
    Parse.Follows SameCode GroupsAlike
      (() => headerGroupEnd kind implicit open auto named colon annotation default close refused consumed)
      (() => headerGroupEnd kind implicit openTwin autoTwin namedTwin colonTwin annotationTwin defaultTwin closeTwin
        refused consumedTwin) :=
  match refused, default, defaultTwin with
    | Some message, Some _, Some _ => followsFatalAny _ _
    | Some message, None, None =>
      Parse.followsDone _ _
        (alikeGroup kind implicit open openTwin [] [] Trivial auto autoTwin autos named namedTwin nameds
          (Some colon) (Some colonTwin) Trivial (Some annotation) (Some annotationTwin) annotations
          None None defaults close closeTwin (default.isNone && consumed) (defaultTwin.isNone && consumedTwin))
    | None, Some _, Some _ =>
      Parse.followsDone _ _
        (alikeGroup kind implicit open openTwin [] [] Trivial auto autoTwin autos named namedTwin nameds
          (Some colon) (Some colonTwin) Trivial (Some annotation) (Some annotationTwin) annotations
          default defaultTwin defaults close closeTwin (default.isNone && consumed) (defaultTwin.isNone && consumedTwin))
    | None, None, None =>
      Parse.followsDone _ _
        (alikeGroup kind implicit open openTwin [] [] Trivial auto autoTwin autos named namedTwin nameds
          (Some colon) (Some colonTwin) Trivial (Some annotation) (Some annotationTwin) annotations
          None None defaults close closeTwin (default.isNone && consumed) (defaultTwin.isNone && consumedTwin))

theorem followsHeaderGroupColon ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin) (inner: Modes) (kind: GroupKind) (refused: Option Text) (implicit: Bool)
    (started startedTwin: Parse.Mark Item) (open openTwin: Comments) (auto autoTwin: Option Comments)
    (autos: Option.Alike Anything auto autoTwin) (named namedTwin: List Word)
    (nameds: List.All2 WordsAlike named namedTwin) (atColon: Bool):
    Parse.Follows SameCode GroupsAlike
      (() => headerGroupColon self inner kind refused implicit started open auto named atColon)
      (() => headerGroupColon selfTwin inner kind refused implicit startedTwin openTwin autoTwin namedTwin atColon) :=
  match !atColon with
    | True => followsFatalAny _ (() => Syntax.fatal "a parameter needs a type")
    | False =>
      Parse.followsThen followsFixedFrom (colon colonTwin colons =>
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
                (followsExpectFixedTwo
                  inner
                  (closerOf implicit)
                  (closeMessage implicit auto named)
                  (closeMessage implicit autoTwin namedTwin))
                (close closeTwin closes =>
                  Parse.followsThen (followsConsumedBare started startedTwin) (consumed consumedTwin consumeds =>
                    followsHeaderGroupEnd
                      kind
                      implicit
                      open
                      openTwin
                      auto
                      autoTwin
                      autos
                      named
                      namedTwin
                      nameds
                      colon
                      colonTwin
                      annotation
                      annotationTwin
                      annotations
                      default
                      defaultTwin
                      defaults
                      close
                      closeTwin
                      refused
                      consumed
                      consumedTwin))))))

theorem autoSplitAlike ∀ (implicit: Bool) (names namesTwin: List Word) (alike: List.All2 WordsAlike names namesTwin):
    PairAlike (Option.Alike Anything) (List.All2 WordsAlike) (autoSplit implicit names) (autoSplit implicit namesTwin) :=
  match names, namesTwin with
    | [], [] => (Trivial, Trivial)
    | [word], [twin] => (Trivial, alike)
    | [word, second, ..more], [twin, secondTwin, ..moreTwin] =>
      rewrite wordText word twin alike.left then
        match implicit && twin.text == "auto" with
          | True => (Trivial, alike.right)
          | False => (Trivial, alike)
    | [word], [twin, second, ..more] => alike.right.impossible
    | [word, second, ..more], [twin] => alike.right.impossible

theorem followsHeaderGroupNamed ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin) (inner: Modes) (kind: GroupKind) (refused: Option Text) (implicit: Bool)
    (started startedTwin: Parse.Mark Item) (open openTwin: Comments) (split splitTwin: (Option Comments, List Word))
    (splits: PairAlike (Option.Alike Anything) (List.All2 WordsAlike) split splitTwin):
    Parse.Follows SameCode GroupsAlike
      (() => headerGroupNamed self inner kind refused implicit started open split)
      (() => headerGroupNamed selfTwin inner kind refused implicit startedTwin openTwin splitTwin) :=
  match split, splitTwin with
    | (auto, named), (autoTwin, namedTwin) =>
      followsThenEq
        [j := atColon => headerGroupColon self inner kind refused implicit started open auto named atColon]
        [k := atColon => headerGroupColon selfTwin inner kind refused implicit startedTwin openTwin autoTwin namedTwin atColon]
        (followsAt inner Colon)
        (atColon =>
          followsHeaderGroupColon knot inner kind refused implicit started startedTwin open openTwin auto autoTwin
            splits.left named namedTwin splits.right atColon)

theorem followsHeaderGroupTyped ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin) (inner: Modes) (kind: GroupKind) (refused: Option Text) (implicit: Bool)
    (started startedTwin: Parse.Mark Item) (open openTwin: Comments) (names namesTwin: List Word)
    (nameses: List.All2 WordsAlike names namesTwin):
    Parse.Follows SameCode GroupsAlike
      (() => headerGroupTyped self inner kind refused implicit started open names)
      (() => headerGroupTyped selfTwin inner kind refused implicit startedTwin openTwin namesTwin) :=
  followsHeaderGroupNamed knot inner kind refused implicit started startedTwin open openTwin
    (autoSplit implicit names)
    (autoSplit implicit namesTwin)
    (autoSplitAlike implicit names namesTwin nameses)

theorem followsHeaderGroupAuto ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin) (inner: Modes) (kind: GroupKind) (open openTwin: Comments) (auto autoTwin: Word):
    Parse.Follows SameCode GroupsAlike
      (() => headerGroupAuto self inner kind open auto)
      (() => headerGroupAuto selfTwin inner kind openTwin autoTwin) :=
  Parse.followsThen (followsFull knot inner) (annotation annotationTwin annotations =>
    Parse.followsThen (followsExpectFixed inner RBracket "`]` to close the parameter `[auto …]`") (close closeTwin closes =>
      Parse.followsDone _ _
        (alikeGroup kind True open openTwin [] [] Trivial (Some auto.comments) (Some autoTwin.comments) Trivial [] []
          Trivial None None Trivial (Some annotation) (Some annotationTwin) annotations None None Trivial close
          closeTwin False False)))

theorem followsHeaderGroupNames ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin) (inner: Modes) (kind: GroupKind) (refused: Option Text) (implicit: Bool)
    (started startedTwin: Parse.Mark Item) (open openTwin: Comments) (names namesTwin: List Word)
    (nameses: List.All2 WordsAlike names namesTwin) (typeFollows: Bool):
    Parse.Follows SameCode GroupsAlike
      (() => headerGroupNames self inner kind refused implicit started open names typeFollows)
      (() => headerGroupNames selfTwin inner kind refused implicit startedTwin openTwin namesTwin typeFollows) :=
  match names, namesTwin with
    | [auto], [autoTwin] =>
      let texts: auto.text = autoTwin.text := wordText auto autoTwin nameses.left
      let guards: (implicit && auto.text == "auto" && typeFollows) = (implicit && autoTwin.text == "auto" && typeFollows) :=
        Eq.cong (text => implicit && text == "auto" && typeFollows) texts
      match first: implicit && auto.text == "auto" && typeFollows, second: implicit && autoTwin.text == "auto" && typeFollows with
          | True, True => followsHeaderGroupAuto knot inner kind open openTwin auto autoTwin
          | False, False =>
            followsHeaderGroupTyped [self := self] [selfTwin := selfTwin] knot inner kind refused implicit started
              startedTwin open openTwin [auto] [autoTwin] nameses
    | [], [] =>
      followsHeaderGroupTyped knot inner kind refused implicit started startedTwin open openTwin [] [] nameses
    | [first, second, ..more], [firstTwin, secondTwin, ..moreTwin] =>
      followsHeaderGroupTyped knot inner kind refused implicit started startedTwin open openTwin
        [first, second, ..more]
        [firstTwin, secondTwin, ..moreTwin]
        nameses
    | [word], [twin, second, ..more] => nameses.right.impossible
    | [word, second, ..more], [twin] => nameses.right.impossible

theorem followsHeaderGroupParts ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin) (modes: Modes) (kind: GroupKind) (refused: Option Text) (implicit: Bool):
    Parse.Follows SameCode GroupsAlike
      (() => headerGroupParts self modes kind refused implicit)
      (() => headerGroupParts selfTwin modes kind refused implicit) :=
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
    (knot: SelfFollows self selfTwin) (modes: Modes) (kind: GroupKind) (refused: Option Text) (first second: Option Tok):
    Parse.Follows SameCode GroupsAlike
      (() => headerGroupOn self modes kind refused first second)
      (() => headerGroupOn selfTwin modes kind refused first second) :=
  match first, second with
    | Some LParen, Some RParen =>
      Parse.followsThen followsFixedFrom (open openTwin opens =>
        Parse.followsThen followsFixedFrom (close closeTwin closes =>
          Parse.followsDone _ _
            (alikeGroup kind False open openTwin [] [] Trivial None None Trivial [] [] Trivial None None Trivial None
              None Trivial None None Trivial close closeTwin False False)))
    | Some LParen, _ => followsHeaderGroupParts knot modes kind refused False
    | Some LBracket, _ => followsHeaderGroupParts knot modes kind refused True
    | _, _ => followsFail modes "a parameter such as `(x: Nat)`, or `:` and the definition's type" (() =>
      modes.fail "a parameter such as `(x: Nat)`, or `:` and the definition's type")

theorem followsHeaderGroupSeen ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin) (modes: Modes) (kind: GroupKind) (refused: Option Text) (first: Option Tok):
    Parse.Follows SameCode GroupsAlike
      (() => headerGroupSeen self modes kind refused first)
      (() => headerGroupSeen selfTwin modes kind refused first) :=
  followsThenEq (followsPeekAt modes 1) (second => followsHeaderGroupOn knot modes kind refused first second)

theorem followsHeaderGroup ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin) (modes: Modes) (kind: GroupKind) (refused: Option Text):
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

theorem alikeRow ∀ (open openTwin: Comments) (abilities twins: List Expr) (alike: List.All2 ExprsAlike abilities twins)
    (variable variableTwin: Option (Comments, Word))
    (variables: Option.Alike (PairAlike Anything WordsAlike) variable variableTwin) (close closeTwin: Comments):
    RowsAlike { open, abilities, variable, close }
      { open = openTwin, abilities = twins, variable = variableTwin, close = closeTwin } :=
  calc (walkRow blankPure { open, abilities, variable, close }).blank
    _ = { open = Comments.none,
          abilities = walkExprs blankPure abilities,
          variable = blankCommentsWord variable,
          close = Comments.none } := byComputing
    _ = { open = Comments.none,
          abilities = walkExprs blankPure twins,
          variable = blankCommentsWord variableTwin,
          close = Comments.none } :=
      rewrite walkExprsAlike abilities twins alike, commentsWordBlank variable variableTwin variables
    _ = (walkRow blankPure { open = openTwin, abilities = twins, variable = variableTwin, close = closeTwin }).blank :=
      byComputing

theorem alikeEffect ∀ (row twin: Row) (rows: RowsAlike row twin) (result resultTwin: Expr)
    (results: ExprsAlike result resultTwin):
    ExprsAlike (Effect row result) (Effect twin resultTwin) :=
  calc (Effect row result).walk blankPure
    _ = Effect (walkRow blankPure row).blank (result.walk blankPure) := byComputing
    _ = Effect (walkRow blankPure twin).blank (resultTwin.walk blankPure) := rewrite rows, results
    _ = (Effect twin resultTwin).walk blankPure := byComputing

theorem alikeFunctionType ∀ (binder twin: Group) (binders: GroupsAlike binder twin) (arrow arrowTwin: Word)
    (arrows: WordsAlike arrow arrowTwin) (result resultTwin: Expr) (results: ExprsAlike result resultTwin):
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
    | True =>
      Parse.followsThen followsFixedFrom (bar barTwin bars =>
        Parse.followsMap
          [alike := Option.Alike (PairAlike Anything WordsAlike)]
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
    Parse.followsDone _ _ (alikeRow open openTwin abilities twins alike variable variableTwin variables close closeTwin))

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

theorem rowEntriesAlike ∀ (pair pairTwin: (List Expr, Bool)) (pairs: PairAlike (List.All2 ExprsAlike) Same pair pairTwin):
    List.All2 ExprsAlike (rowEntries pair) (rowEntries pairTwin) :=
  match pair, pairTwin with
    | (entries, closed), (twins, closedTwin) => pairs.left

theorem followsRowAbilities ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin) (modes: Modes) (closed pipe: Bool):
    Parse.Follows SameCode (List.All2 ExprsAlike) (() => rowAbilities self modes closed pipe) (() =>
      rowAbilities selfTwin modes closed pipe) :=
  match closed || pipe with
    | True => Parse.followsDone [] [] Trivial
    | False =>
      Parse.followsThen (knot { modes, level = LevelApp }) (first firstTwin firsts =>
        Parse.followsThen
          [p := () => Parse.mark()]
          [q := () => Parse.mark()]
          [j := here => rowEntries (commaList (here.left + 1) modes (count => False) (() => self { modes, level = LevelApp }) first [])]
          [k := here => rowEntries (commaList (here.left + 1) modes (count => False) (() => selfTwin { modes, level = LevelApp }) firstTwin [])]
          Parse.followsMark
          (here hereTwin marks =>
            rewrite marks.right.right then
              Parse.followsMap
                [alike := List.All2 ExprsAlike]
                (pair => rowEntries pair)
                (pair => rowEntries pair)
                (pair pairTwin pairs => rowEntriesAlike pair pairTwin pairs)
                (followsCommaList modes (count => False) (count => False)
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
    (knot: SelfFollows self selfTwin) (modes: Modes) (open openTwin: Comments) (lower: Bool) (second: Option Tok):
    Parse.Follows SameCode RowsAlike (() => rowStart self modes open lower second) (() =>
      rowStart selfTwin modes openTwin lower second) :=
  match lower && isSome Colon second with
    | True =>
      followsFatalAny _ (() => Syntax.fatal "a record type can't be written here: `{` in a type starts an ability row")
    | False =>
      followsThenEq
        [j := closed => (let abilities := rowAbilities self modes closed (modes.at Pipe); rowVariable modes open abilities)]
        [k := closed =>
          (let abilities := rowAbilities selfTwin modes closed (modes.at Pipe); rowVariable modes openTwin abilities)]
        (followsAt modes RBrace)
        (closed =>
          followsThenEq
            [j := pipe => (let abilities := rowAbilities self modes closed pipe; rowVariable modes open abilities)]
            [k := pipe => (let abilities := rowAbilities selfTwin modes closed pipe; rowVariable modes openTwin abilities)]
            (followsAt modes Pipe)
            (pipe =>
              Parse.followsThen (followsRowAbilities knot modes closed pipe) (abilities twins alike =>
                followsRowVariable modes open openTwin abilities twins alike)))

theorem followsRowOf ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin) (modes: Modes):
    Parse.Follows SameCode RowsAlike (() => rowOf self modes) (() => rowOf selfTwin modes) :=
  Parse.followsThen (followsExpectFixed modes LBrace "`{`") (open openTwin opens =>
    followsThenEq
      [j := lower => rowStart self modes open lower (modes.peekAt 1)]
      [k := lower => rowStart selfTwin modes openTwin lower (modes.peekAt 1)]
      (followsAt modes Lower)
      (lower =>
        followsThenEq (followsPeekAt modes 1) (second => followsRowStart knot modes open openTwin lower second)))

theorem followsEffectResult ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin) (allowed: Modes):
    Parse.Follows SameCode ExprsAlike (() => effectResult self allowed) (() => effectResult selfTwin allowed) :=
  Parse.followsThen (followsRowOf knot allowed) (row rowTwin rows =>
    Parse.followsMap
      [alike := ExprsAlike]
      (result => Effect row result)
      (result => Effect rowTwin result)
      (result resultTwin results => alikeEffect row rowTwin rows result resultTwin results)
      (followsFull knot allowed))

theorem followsResultRow ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin) (allowed: Modes) (row: Bool):
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
  match attributes with
    | [] => byComputing
    | [x, ..xs] => byComputing

theorem followsRefuseEmpty ∀ (attributes twins: List Attributes) (empties: attributes.isEmpty = twins.isEmpty)
    (what: Text):
    Parse.Follows SameCode Anything (() => refuseAttributes attributes what) (() => refuseAttributes twins what) :=
  match attributes, twins with
    | [], [] => Parse.followsDone () () Trivial
    | [x, ..xs], [y, ..ys] => followsFatalAny _ _
    | [], [y, ..ys] => cases
    | [x, ..xs], [] => cases

theorem groupWalkAttributes ∀ (group: Group):
    (group.walk blankPure).blank.attributes = walkAttributes blankPure group.attributes :=
  match group with
    | { kind, implicit, open, attributes, auto, names, colon, annotation, default, close, bare } => byComputing

theorem groupAttributesEmpty ∀ (group twin: Group) (alike: GroupsAlike group twin):
    group.attributes.isEmpty = twin.attributes.isEmpty :=
  let same: walkAttributes blankPure group.attributes = walkAttributes blankPure twin.attributes :=
    calc walkAttributes blankPure group.attributes
      _ = (group.walk blankPure).blank.attributes := Eq.flipped (groupWalkAttributes group)
      _ = (twin.walk blankPure).blank.attributes := Eq.cong (found => found.attributes) alike
      _ = walkAttributes blankPure twin.attributes := groupWalkAttributes twin
  calc group.attributes.isEmpty
    _ = (walkAttributes blankPure group.attributes).isEmpty := Eq.flipped (walkAttributesEmpty group.attributes)
    _ = (walkAttributes blankPure twin.attributes).isEmpty := rewrite same
    _ = twin.attributes.isEmpty := walkAttributesEmpty twin.attributes

theorem optionIsSome ∀ [r: a → b → Prop] (found: Option a) (twin: Option b) (alike: Option.Alike r found twin):
    found.isSome = twin.isSome :=
  match found, twin with
    | Some x, Some y => byComputing
    | None, None => byComputing

theorem followsBinderDefault ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin) (inner: Modes) (atColonEq: Bool):
    Parse.Follows SameCode (Option.Alike (PairAlike Anything ExprsAlike))
      (() => binderDefault self inner atColonEq)
      (() => binderDefault selfTwin inner atColonEq) :=
  match atColonEq with
    | True =>
      Parse.followsThen followsFixedFrom (colonEq colonEqTwin colonEqs =>
        Parse.followsMap
          [alike := Option.Alike (PairAlike Anything ExprsAlike)]
          [p := () => full self inner]
          [q := () => full selfTwin inner]
          (value => Some (colonEq, value))
          (value => Some (colonEqTwin, value))
          (value valueTwin values => (colonEqs, values))
          (followsFull knot inner))
    | False => Parse.followsDone None None Trivial

theorem followsBinderGroup ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin) (modes: Modes) (defaults: Bool):
    Parse.Follows SameCode GroupsAlike (() => binderGroup self modes defaults) (() => binderGroup selfTwin modes defaults) :=
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
                   else {
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
                   else {
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
                  Parse.followsThen (followsBinderDefault knot modes.inBrackets atEquals) (default defaultTwin defaults2 =>
                    Parse.followsThen (followsExpectFixed modes.inBrackets RParen "`)`") (close closeTwin closes =>
                      let same: default.isSome = defaultTwin.isSome := optionIsSome default defaultTwin defaults2
                      rewrite same then
                        match !defaults && defaultTwin.isSome with
                          | True => followsFatalAny _ _
                          | False =>
                            Parse.followsDone _ _
                              (alikeGroup GroupBinder False open openTwin attributes attributesTwin attributeses None
                                None Trivial [first, ..more] [firstTwin, ..moreTwin] (Both firsts mores)
                                (Some colon) (Some colonTwin) Trivial (Some annotation) (Some annotationTwin)
                                annotations default defaultTwin defaults2 close closeTwin False False))))))))))

theorem implicitAutoAlike ∀ (first firstTwin: Word) (firsts: WordsAlike first firstTwin) (rest restTwin: List Word)
    (rests: List.All2 WordsAlike rest restTwin):
    PairAlike (Option.Alike Anything) (List.All2 WordsAlike) (implicitAuto first rest) (implicitAuto firstTwin restTwin) :=
  match rest, restTwin with
    | [], [] => (Trivial, Both firsts Trivial)
    | [second, ..more], [secondTwin, ..moreTwin] =>
      let texts: first.text = firstTwin.text := wordText first firstTwin firsts
      let guards: (first.text == "auto") = (firstTwin.text == "auto") := Eq.cong (text => text == "auto") texts
      match which: first.text == "auto", twin: firstTwin.text == "auto" with
        | True, True => (Trivial, rests)
        | False, False => (Trivial, Both firsts rests)

theorem followsImplicitNamed ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin) (inner: Modes) (open openTwin: Comments) (attributes attributesTwin: List Attributes)
    (attributeses: List.All2 AttributesAlike attributes attributesTwin) (split splitTwin: (Option Comments, List Word))
    (splits: PairAlike (Option.Alike Anything) (List.All2 WordsAlike) split splitTwin):
    Parse.Follows SameCode GroupsAlike
      (() => implicitNamed self inner open attributes split)
      (() => implicitNamed selfTwin inner openTwin attributesTwin splitTwin) :=
  match split, splitTwin with
    | (auto, names), (autoTwin, namesTwin) =>
      Parse.followsThen (followsExpectFixed inner Colon "`:`") (colon colonTwin colons =>
        Parse.followsThen (followsBinderType knot inner) (annotation annotationTwin annotations =>
          Parse.followsThen (followsExpectFixed inner RBracket "`]`") (close closeTwin closes =>
            Parse.followsDone _ _
              (alikeGroup GroupBinder True open openTwin attributes attributesTwin attributeses auto autoTwin
                splits.left names namesTwin splits.right (Some colon) (Some colonTwin) Trivial (Some annotation)
                (Some annotationTwin) annotations None None Trivial close closeTwin False False))))

theorem followsImplicitBinderOf ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin) (modes: Modes) (nameless: Bool):
    Parse.Follows SameCode GroupsAlike (() => implicitBinderOf self modes nameless) (() =>
      implicitBinderOf selfTwin modes nameless) :=
  match nameless with
    | True =>
      Parse.followsThen followsFixedFrom (open openTwin opens =>
        Parse.followsThen followsFixedFrom (auto autoTwin autos =>
          Parse.followsThen (followsFull knot modes.inBrackets) (annotation annotationTwin annotations =>
            Parse.followsThen (followsExpectFixed modes.inBrackets RBracket "`]`") (close closeTwin closes =>
              Parse.followsDone _ _
                (alikeGroup GroupBinder True open openTwin [] [] Trivial (Some auto) (Some autoTwin) Trivial [] []
                  Trivial None None Trivial (Some annotation) (Some annotationTwin) annotations None None Trivial
                  close closeTwin False False)))))
    | False =>
      Parse.followsThen (followsExpectFixed modes LBracket "`[`") (open openTwin opens =>
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
    (items others same =>
      rewrite deafOfStripped namelessAutoAt namelessAutoAtDeaf items others same then
        followsImplicitBinderOf knot modes (namelessAutoAt others))

theorem followsPiBinder ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin) (modes: Modes) (implicit: Bool):
    Parse.Follows SameCode GroupsAlike (() => piBinder self modes implicit) (() => piBinder selfTwin modes implicit) :=
  match implicit with
    | True => followsImplicitBinder knot modes
    | False => followsBinderGroup knot modes False

theorem followsPiExpr ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin) (modes: Modes) (implicit: Bool):
    Parse.Follows SameCode ExprsAlike (() => piExpr self modes implicit) (() => piExpr selfTwin modes implicit) :=
  Parse.followsThen (followsPiBinder knot modes implicit) (binder binderTwin binders =>
    Parse.followsThen
      (followsRefuseEmpty binder.attributes binderTwin.attributes (groupAttributesEmpty binder binderTwin binders)
        "a function type's parameter")
      (refusal refusalTwin refusals =>
        Parse.followsThen (followsExpect modes Arrow "`->`") (arrow arrowTwin arrows =>
          Parse.followsMap
            [alike := ExprsAlike]
            (result => FunctionType binder arrow result)
            (result => FunctionType binderTwin arrowTwin result)
            (result resultTwin results => alikeFunctionType binder binderTwin binders arrow arrowTwin arrows result resultTwin results)
            (followsResultType knot modes))))
