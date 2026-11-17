--| P4 keeps `meaning`, and so do the four passes together
--| (`tidyKeepsMeaning`).
--|
--| P4 merges two groups only where `meaningJoins` holds: `meaning` reads
--| them alike but for their names and splits each and their merge into one
--| group a name. Then the merge's pieces are the two groups' pieces
--| (`mergePieces`), and by induction along the list so are a merged list's
--| (`mergeFromKeeps`, `mergeParamsFromKeeps`).
namespace Fmt.Proofs
import Fmt (..)
import Fmt.Walk (..)
import Std (Bool, Eq, Fail, List, Nat, Option, Result, Text)
import Syntax (..)

--| A group as `meaning`'s walk leaves it before splitting.
def groupMeaning (group: Group): Group := (group.walk meaningPure).blank.plainType

theorem formIs ∀ (group: Group): group.meaningForm = Some (groupMeaning group) :=
  rewrite groupOk meaningSteps meaningPure meaningAgrees group

theorem splitsIs ∀ (group: Group): group.meaningSplits = (groupMeaning group).splits := rewrite formIs group

theorem namesIs ∀ (group: Group): (groupMeaning group).names = blankWords group.names := match group with
  | { kind, implicit, open, attributes, auto, names, colon, annotation, default, close, bare } => byComputing

theorem wordsAppend ∀ (first second: List Word): blankWords (first ++ second) = blankWords first ++ blankWords second :=
  match first with
    | [] => byComputing
    | [word, ..rest] => rewrite wordsAppend rest second

--| A group `meaning` splits is one group a name.
theorem piecesOf ∀ (group: Group) (first: Word) (rest: List Word)
    (splits: group.splits = True)
    (named: group.names = [first, ..rest]):
    group.pieces = [first, ..rest].map (name => { group | names = [name] }) :=
  rewrite named, splits

theorem renamed ∀ (one other: Group)
    (same: one.withoutNames = other.withoutNames) (names: List Word):
    { one | names } = { other | names } :=
  Eq.cong ((group: Group) => { group | names }) same

--| Two groups `meaning` reads alike but for their names, each split, and
--| split when merged: the merge's pieces are theirs.
theorem mergePieces ∀ (current next: Group)
    (currentNamed: current.names.isEmpty = False)
    (nextNamed: next.names.isEmpty = False)
    (same: (groupMeaning next).withoutNames = (groupMeaning current).withoutNames)
    (currentSplits: (groupMeaning current).splits = True)
    (nextSplits: (groupMeaning next).splits = True)
    (mergedSplits: (groupMeaning { current | names = current.names ++ next.names }).splits = True):
    (groupMeaning { current | names = current.names ++ next.names }).pieces
      = (groupMeaning current).pieces ++ (groupMeaning next).pieces :=
  match current, next with
    | { kind, implicit, open, attributes, auto, names, colon, annotation, default, close, bare }, {
        kind = kind2,
        implicit = implicit2,
        open = open2,
        attributes = attributes2,
        auto = auto2,
        names = names2,
        colon = colon2,
        annotation = annotation2,
        default = default2,
        close = close2,
        bare = bare2
      } =>
      match names, names2 with
        | [], _ => cases
        | _, [] => cases
        | [first, ..rest], [second, ..others] =>
          rewrite piecesOf _ first.blank (blankWords (rest ++ [second, ..others])) mergedSplits (namesIs _),
              piecesOf _ first.blank (blankWords rest) currentSplits (namesIs _),
              piecesOf _ second.blank (blankWords others) nextSplits (namesIs _),
              wordsAppend rest [second, ..others],
              List.mapAppend _ _ _,
              renamed _ _ same

--| What `joins` gives the proof.
theorem joinedPieces ∀ (current next: Group)
    (joined: joins current next = True):
    (groupMeaning { current | names = current.names ++ next.names }).pieces
      = (groupMeaning current).pieces ++ (groupMeaning next).pieces :=
  match joined with
    | Both rust facts =>
      match facts with
        | Both currentNamed (Both nextNamed (Both same (Both currentSplits (Both nextSplits mergedSplits)))) =>
          let alike: next.meaningForm.map Group.withoutNames = current.meaningForm.map Group.withoutNames := same.read
          let mapped := (form: Option Group) => form.map Group.withoutNames
          let alike': Some (groupMeaning next).withoutNames = Some (groupMeaning current).withoutNames := calc Some
            (groupMeaning next).withoutNames
            _ = next.meaningForm.map Group.withoutNames := Eq.flipped (Eq.cong mapped (formIs next))
            _ = current.meaningForm.map Group.withoutNames := alike
            _ = Some (groupMeaning current).withoutNames := Eq.cong mapped (formIs current)
          mergePieces current next currentNamed.read nextNamed.read
            (Eq.cong (form => form.getOrElse (groupMeaning next).withoutNames) alike')
            (rewrite <- splitsIs current then currentSplits)
            (rewrite <- splitsIs next then nextSplits)
            (rewrite <- splitsIs { current | names = current.names ++ next.names } then mergedSplits)

-- Along a header's groups.

theorem mergeFromKeeps ∀ (current: Group) (rest: List Group):
    splitGroups ((mergeFrom current rest).map groupMeaning) = splitGroups ([current, ..rest].map groupMeaning) :=
  match rest with
    | [] => byComputing
    | [next, ..more] =>
      match joined: joins current next with
        | True =>
          rewrite mergeFromKeeps { current | names = current.names ++ next.names } more,
              joinedPieces current next joined,
              List.appendAssoc
                (groupMeaning current).pieces
                (groupMeaning next).pieces
                (splitGroups (more.map groupMeaning))
        | False => rewrite mergeFromKeeps next more

theorem mergeGroupsKeeps ∀ (groups: List Group):
    splitGroups ((mergeGroups groups).map groupMeaning) = splitGroups (groups.map groupMeaning) :=
  match groups with
    | [] => byComputing
    | [first, ..rest] => mergeFromKeeps first rest

theorem groupsMeaning ∀ (groups: List Group):
    (blankGroups (walkGroups meaningPure groups)).map Group.plainType = groups.map groupMeaning :=
  match groups with
    | [] => byComputing
    | [first, ..rest] => rewrite groupsMeaning rest

theorem mergeHeaderWalk ∀ (header: Header):
    walkHeader meaningPure (mergeHeader header) = walkHeader meaningPure header :=
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
      match kind with
        | DefInstance => byComputing
        | DefPlain => rewrite groupsMeaning (mergeGroups params), groupsMeaning params, mergeGroupsKeeps params
        | DefTheorem => rewrite groupsMeaning (mergeGroups params), groupsMeaning params, mergeGroupsKeeps params

-- Along a `∀`'s or lambda's parameters.

--| A parameter as `meaning`'s walk leaves it before splitting.
def paramMeaning: Param → Param
  | NameParam word => NameParam word.blank
  | PatternParam pattern => PatternParam (pattern.walk meaningPure)
  | Grouped group => Grouped (groupMeaning group)
  | TypedPattern open pattern colon annotation close =>
    TypedPattern open.blank (pattern.walk meaningPure) colon.blank (annotation.walk meaningPure).unwrapped close.blank

theorem paramsMeaning ∀ (params: List Param):
    (blankParams (walkParams meaningPure params)).map Param.plainType = params.map paramMeaning :=
  match params with
    | [] => byComputing
    | [NameParam word, ..rest] => rewrite paramsMeaning rest
    | [PatternParam pattern, ..rest] => rewrite paramsMeaning rest
    | [Grouped group, ..rest] => rewrite paramsMeaning rest
    | [TypedPattern open pattern colon annotation close, ..rest] => rewrite paramsMeaning rest

theorem mergeParamsFromKeeps ∀ (current: Group) (rest: List Param):
    splitParams ((mergeParamsFrom current rest).map paramMeaning)
      = splitParams ([Grouped current, ..rest].map paramMeaning) :=
  match rest with
    | [] => byComputing
    | [Grouped next, ..more] =>
      match joined: joins current next with
        | True =>
          rewrite mergeParamsFromKeeps { current | names = current.names ++ next.names } more,
              joinedPieces current next joined,
              List.mapAppend (groupMeaning current).pieces (groupMeaning next).pieces Grouped,
              List.appendAssoc
                ((groupMeaning current).pieces.map Grouped)
                ((groupMeaning next).pieces.map Grouped)
                (splitParams (more.map paramMeaning))
        | False => rewrite mergeParamsFromKeeps next more
    | [NameParam word, ..more] => rewrite mergeParamsKeeps more
    | [PatternParam pattern, ..more] => rewrite mergeParamsKeeps more
    | [TypedPattern open pattern colon annotation close, ..more] => rewrite mergeParamsKeeps more

theorem mergeParamsKeeps ∀ (params: List Param):
    splitParams ((mergeParams params).map paramMeaning) = splitParams (params.map paramMeaning) :=
  match params with
    | [] => byComputing
    | [Grouped first, ..rest] => mergeParamsFromKeeps first rest
    | [NameParam word, ..rest] => rewrite mergeParamsKeeps rest
    | [PatternParam pattern, ..rest] => rewrite mergeParamsKeeps rest
    | [TypedPattern open pattern colon annotation close, ..rest] => rewrite mergeParamsKeeps rest

theorem mergeBindingWalk ∀ (expr: Expr): (mergeBinding expr).walk meaningPure = expr.walk meaningPure := match expr with
  | Binding kind keyword params arrow body =>
    match kind with
      | BindsExists => byComputing
      | BindsLambda => rewrite paramsMeaning (mergeParams params), paramsMeaning params, mergeParamsKeeps params
      | BindsForall => rewrite paramsMeaning (mergeParams params), paramsMeaning params, mergeParamsKeeps params
  | _ => cases

-- P4, and the four passes.

def mergeSteps: Steps := { Steps.keep | header = mergeHeader, expr = mergeBinding }

def mergePure: Pure := { Pure.keep | header = mergeHeader, expr = mergeBinding }

def mergeAgrees: Agrees mergeSteps mergePure := {
  expr = (z => byComputing),
  pattern = (z => byComputing),
  header = (z => byComputing),
  decl = (z => byComputing),
  fields = (z => byComputing),
  attributes = (z => byComputing),
  ruleSet = (z => byComputing)
}

def mergeKeeps: Keeps mergePure meaningPure := {
  expr = mergeBindingWalk,
  pattern = (z => byComputing),
  header = mergeHeaderWalk,
  decl = (z => byComputing),
  fields = (z => byComputing),
  attributes = (z => byComputing),
  ruleSet = (z => byComputing)
}

--| P4 keeps `meaning`.
theorem mergeKeepsFile ∀ (file: SourceFile): file.withMergedParameters.meaning = file.meaning :=
  rewrite applyKeeps file.withoutEnd mergeSteps meaningSteps mergePure meaningPure mergeAgrees meaningAgrees mergeKeeps

--| The four passes keep `meaning`.
theorem tidyKeepsMeaning ∀ (file: SourceFile): file.tidy.meaning = file.meaning :=
  rewrite mergeKeepsFile file.withForall.withoutTrailingCommas.withoutSpareBrackets, firstThreeKeepMeaning file
