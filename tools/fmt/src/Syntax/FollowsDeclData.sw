namespace Syntax.FollowsDeclData
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
import Syntax.FollowsDeclArms (..)

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
        (followsExpressionAt rule { modes, level = LevelFull })
        (value valueTwin values => (colonEqs, values)))
    | False => Parse.followsDone Trivial

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
    | False => Parse.followsDone (List.all2Reverse done twins dones, byComputing)

theorem followsFieldsAt ∀ (rule: ExpressionRule) (more: Nat) (modes: Modes)
    (again: FieldsFromFollow modes more) (found twins: List Field)
    (founds: List.All2 FieldAlike found twins) (closed: Bool):
    Parse.Follows SameCode (PairAlike (List.All2 FieldAlike) Same) (() => fieldsAt more modes found closed) (() =>
      fieldsAt more modes twins closed) :=
  match closed with
    | True => Parse.followsDone (List.all2Reverse found twins founds, byComputing)
    | False => Parse.followsThen (followsAttributesOf modes) (attributes attributesTwin attributeses =>
      Parse.followsThen (followsLower modes "a field name") (name nameTwin names =>
        Parse.followsThen (followsExpectFixed modes Colon "`:`") (colon colonTwin colons =>
          Parse.followsThen
            (followsExpressionAt rule { modes, level = LevelFull })
            (annotation annotationTwin annotations =>
              followsThenEq (followsAt modes ColonEq) (atEquals =>
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
    | Zero => Parse.followsDone (List.all2Reverse found twins founds, byComputing)

theorem followsBracedFieldsIn ∀ (rule: ExpressionRule) (inner: Modes) (closed: Bool):
    Parse.Follows SameCode (PairAlike (List.All2 FieldAlike) Same) (() => bracedFieldsIn inner closed) (() =>
      bracedFieldsIn inner closed) :=
  match closed with
    | True => Parse.followsDone (Trivial, byComputing)
    | False => followsFuel (fuel => fieldsFrom fuel inner []) (fuel => fieldsFrom fuel inner []) (fuel =>
      followsFieldsFrom rule fuel inner [] [] Trivial)

theorem followsBracedFields ∀ (rule: ExpressionRule) (modes: Modes):
    Parse.Follows SameCode FieldsAlike (() => bracedFields modes) (() => bracedFields modes) :=
  Parse.followsThen (followsExpectFixed modes LBrace "`{`") (open openTwin opens =>
    followsThenEq (followsAt modes.inBrackets RBrace) (closed =>
      Parse.followsThen (followsBracedFieldsIn rule modes.inBrackets closed) (pair pairTwin pairs =>
        match pair, pairTwin with
          | (fields, trailing), (twins, trailingTwin) =>
            Parse.followsMap
              (close => { open, fields, trailingComma = trailing, close })
              (close => { open = openTwin, fields = twins, trailingComma = trailingTwin, close })
              (followsExpectFixed modes.inBrackets RBrace "`,` or `}`")
              (close closeTwin closes =>
                alikeFields open openTwin fields twins pairs.left trailing trailingTwin pairs.right close closeTwin))))

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
      | False => Parse.followsDone byComputing)

theorem followsParenAhead ∀ (modes: Modes):
    Parse.Follows SameCode Same (() => isSome LParen modes.peek && piBinderAhead left()) (() =>
      isSome LParen modes.peek && piBinderAhead left()) :=
  followsThenEq (followsPeek modes) (seen =>
    match isSome LParen seen with
      | True => followsLook piBinderAhead piBinderAheadDeaf
      | False => Parse.followsDone byComputing)

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
    | False => Parse.followsDone (List.all2Reverse found twins founds)

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
    | Succ more => followsThenEq (followsAt modes LBrace) (brace =>
      followsConstructorBraced rule more modes name nameTwin
        (again1 again2 agains3 agains4 agains5 =>
          followsConstructorParts rule more modes name nameTwin again1 again2 agains3 agains4 agains5)
        bracketed
        braced
        found
        twins
        founds
        (brace && !braced))
    | Zero => Parse.followsDone (List.all2Reverse found twins founds)

theorem followsConstructorResult ∀ (rule: ExpressionRule) (modes: Modes) (atColon: Bool):
    Parse.Follows SameCode (Option.Alike (PairAlike Anything ExprsAlike)) (() => constructorResult modes atColon) (() =>
      constructorResult modes atColon) :=
  match atColon with
    | True => Parse.followsThen followsFixedFrom (colon colonTwin colons =>
      Parse.followsMap
        (result => Some (colon, result))
        (result => Some (colonTwin, result))
        (followsExpressionAt rule { modes, level = LevelApp })
        (result resultTwin results => (colons, results)))
    | False => Parse.followsDone Trivial

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
                        (followsConstructorResult rule modes atColon)
                        (result resultTwin results =>
                          alikeConstructor bar barTwin attributes attributesTwin attributeses name nameTwin names fields
                              fieldsTwin fieldses result resultTwin results)))))))
    | False => Parse.followsDone Trivial

theorem followsConstructorsAt ∀ (rule: ExpressionRule) (modes: Modes) (atBar: Bool):
    Parse.Follows SameCode (List.All2 ConstructorAlike) (() => constructorsAt modes atBar) (() =>
      constructorsAt modes atBar) :=
  match atBar with
    | True => Parse.followsLoop (followsThenEq (followsAt modes Pipe) (bar => followsConstructorStep rule modes bar))
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
        | False, False => Parse.followsDone Trivial
    | [], [] => Parse.followsDone Trivial

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
                  | False => Parse.followsDone binders))
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
        (refusal refusalTwin refusals => Parse.followsDone binders))
    | False => followsThenEq (followsBracketAhead modes) (bracket => followsDataParamBracket rule modes word bracket)

theorem followsDataParams ∀ (rule: ExpressionRule) (modes: Modes) (word: Text) (name nameTwin: Word):
    Parse.Follows SameCode (List.All2 GroupsAlike) (() => dataParams modes word name) (() =>
      dataParams modes word nameTwin) :=
  Parse.followsLoop (followsThenEq (followsAt modes LParen) (atParen => followsDataParamStep rule modes word atParen))

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
    | False => Parse.followsDone (List.all2Reverse found twins founds, indexes)

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
              | False => Parse.followsDone synonyms))

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
        (followsBracedFields rule modes)
        (fields fieldsTwin fieldses =>
          alikeData attributes attributesTwin attributeses False keyword keywordTwin name nameTwin names params
              paramsTwin paramses indices indicesTwin indiceses
              (RecordBody equals fields)
              (RecordBody equalsTwin fieldsTwin)
              (alikeRecordBody equals equalsTwin fields fieldsTwin fieldses))

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
          Parse.followsDone
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
          Parse.followsDone
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
      Parse.followsDone
        (alikeData attributes attributesTwin attributeses False keyword keywordTwin name nameTwin names params
            paramsTwin paramses indices indicesTwin indiceses Abstract Abstract alikeAbstract)
    | False => Parse.followsThen followsFixedFrom (equals equalsTwin equalses =>
      followsThenEq (followsAt modes LBrace) (brace =>
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
        (fields => Data attributes True keyword name params indices (RecordBody equals fields))
        (fields => Data attributesTwin True keywordTwin nameTwin paramsTwin indicesTwin (RecordBody equalsTwin fields))
        (followsBracedFields rule modes)
        (fields fieldsTwin fieldses =>
          alikeData attributes attributesTwin attributeses True keyword keywordTwin name nameTwin names params
              paramsTwin paramses indices indicesTwin indiceses
              (RecordBody equals fields)
              (RecordBody equalsTwin fieldsTwin)
              (alikeRecordBody equals equalsTwin fields fieldsTwin fieldses))

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
                Parse.followsDone (alikeIndices colon colonTwin steps twins pairs.left last lastTwin pairs.right))))
    | False => Parse.followsDone byComputing

theorem followsDataDeclOn ∀ (rule: ExpressionRule) (modes: Modes) (attributes attributesTwin: List Attributes)
    (attributeses: List.All2 AttributeGroupAlike attributes attributesTwin) (isInterface: Bool):
    Parse.Follows SameCode DeclsAlike (() => dataDeclOn modes attributes isInterface) (() =>
      dataDeclOn modes attributesTwin isInterface) :=
  Parse.followsThen followsFixedFrom (keyword keywordTwin keywords =>
    Parse.followsThen (followsDataName modes isInterface) (name nameTwin names =>
      Parse.followsThen
        (followsDataParams rule modes (if isInterface then "interface" else "type") name nameTwin)
        (params paramsTwin paramses =>
          followsThenEq (followsAt modes Colon) (atColon =>
            Parse.followsThen (followsDataIndicesPart rule modes atColon) (indices indicesTwin indiceses =>
              rewrite indexedAlike indices indicesTwin indiceses then
                match isInterface with
                  | True =>
                    followsInterfaceDecl rule modes attributes attributesTwin attributeses keyword keywordTwin name
                        nameTwin names params paramsTwin paramses indices indicesTwin indiceses
                        (indicesTwin.map (found => !found.steps.isEmpty) |> .getOrElse False)
                  | False =>
                    followsTypeDecl rule modes attributes attributesTwin attributeses keyword keywordTwin name nameTwin
                        names params paramsTwin paramses indices indicesTwin indiceses
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
          (followsExpressionAt rule { modes = { modes | allow = Some here }, level = LevelInline })
          (annotation annotationTwin annotations =>
            alikeOperation name nameTwin names colon colonTwin annotation annotationTwin annotations))))

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
            Parse.followsMap (found => Some found) (found => Some found) (followsOperation rule modes) (x y alike =>
              alike)
          | False => Parse.followsDone Trivial
    | [], [] => Parse.followsDone Trivial

theorem followsOperations ∀ (rule: ExpressionRule) (modes: Modes) (column: Nat):
    Parse.Follows SameCode (List.All2 OperationAlike) (() => operations modes column) (() => operations modes column) :=
  Parse.followsThen (followsOperation rule modes) (first firstTwin firsts =>
    Parse.followsMap
      (rest => [first, ..rest])
      (rest => [firstTwin, ..rest])
      (Parse.followsLoop
        (followsOn
          (items => operationNext modes column items)
          (items => operationNext modes column items)
          (itemList others same => followsOperationNext rule modes column itemList others same)))
      (rest restTwin rests => Both firsts rests))

theorem followsAbilityParamStep ∀ (rule: ExpressionRule) (modes: Modes) (atParen: Bool):
    Parse.Follows SameCode (Option.Alike GroupsAlike) (() => abilityParamStep modes atParen) (() =>
      abilityParamStep modes atParen) :=
  match atParen with
    | True => Parse.followsThen (followsBinderGroup (expressionKnot rule) modes False) (binder binderTwin binders =>
      Parse.followsThen
        (followsRefuseEmpty binder.attributes binderTwin.attributes
          (groupAttributesEmpty binder binderTwin binders)
          "an ability's parameter")
        (refusal refusalTwin refusals => Parse.followsDone binders))
    | False => Parse.followsDone Trivial

theorem followsAbilityParams ∀ (rule: ExpressionRule) (modes: Modes):
    Parse.Follows SameCode (List.All2 GroupsAlike) (() => abilityParams modes) (() => abilityParams modes) :=
  Parse.followsLoop (followsThenEq (followsAt modes LParen) (atParen => followsAbilityParamStep rule modes atParen))

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
              (found => Ability keyword name params whereKeyword found)
              (found => Ability keywordTwin nameTwin paramsTwin whereTwin found)
              (followsOperations rule { modes | limit = Some firstTwin.leaf.token.column } firstTwin.leaf.token.column)
              (found foundTwin founds =>
                alikeAbility keyword keywordTwin name nameTwin names params paramsTwin paramses whereKeyword whereTwin
                    found foundTwin founds)
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
        (followsExpressionAt rule { modes, level = LevelFull })
        (body bodyTwin bodies =>
          alikeTest keyword keywordTwin name nameTwin names colonEq colonEqTwin body bodyTwin bodies))

theorem followsTestName ∀ (modes: Modes) (atStr: Bool):
    Parse.Follows SameCode WordsAlike (() => testName modes atStr) (() => testName modes atStr) :=
  match atStr with
    | True => followsBump
    | False => followsFail modes "the test's name, in quotes" (() => modes.fail "the test's name, in quotes")

theorem followsTestDecl ∀ (rule: ExpressionRule) (modes: Modes):
    Parse.Follows SameCode DeclsAlike (() => testDecl modes) (() => testDecl modes) :=
  Parse.followsThen followsFixedFrom (keyword keywordTwin keywords =>
    followsThenEq (followsAt modes Str) (atStr =>
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
        (followsRuleSet (expressionKnot rule) (modes wanted what => followsExpectFixed modes wanted what) modes)
        (rules rulesTwin ruleses =>
          alikeRuleSetDecl keyword keywordTwin name nameTwin names colonEq colonEqTwin rules rulesTwin ruleses)
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
    followsThenEq (followsAt modes Upper) (atUpper =>
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
          Parse.followsDone
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
                Parse.followsDone
                  (alikeDefinition attributes attributesTwin attributeses header headerTwin partses.left body bodyTwin
                      partses.right)
              | False => followsFatalAny _ _)

-- One declaration.

theorem followsAfterOpaqueOn ∀ (modes: Modes) (seen: Option Tok):
    Parse.Follows SameCode Anything (() => afterOpaqueOn modes seen) (() => afterOpaqueOn modes seen) :=
  match seen with
    | Some KwDef => Parse.followsDone Trivial
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
      | True => followsThenEq (followsPeekAt modes 1) (second => Parse.followsDone byComputing)
      | False => Parse.followsDone byComputing)

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
  byWalking [followsFatalAny, followsNamespaceLine]

theorem followsImportStep ∀ (seen: Seen) (modes: Modes):
    Parse.Follows SameCode DeclsAlike (() => importStep seen modes) (() => importStep seen modes) :=
  byWalking [followsFatalAny, followsImportLine]

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
      | True => Parse.followsDone decls
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
      | None => followsThenEq (followsPeek modes) (kind =>
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

-- The facts that other files assume of this file's functions, each proved from the lemmas above.

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
