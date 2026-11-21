--| The passes' steps keep `meaning` at the node they rewrite (stage 4b,
--| SW-3864): P1's and P2's by computing over the node's form; P3's at a
--| row by induction along the result's left end.
--|
--| Then each of P1, P2 and P3 keeps `meaning` file by file
--| (`forallKeepsFile`, `commaKeepsFile`, `bracketKeepsFile`, and the three
--| together, `firstThreeKeepMeaning`), through the traversal lemma
--| `Fmt.Walk.applyKeeps`: each step, as a pure function, keeps what
--| `meaning`'s walk gives of the whole node it rewrites, descendants
--| included (`Keeps`). P3's steps rebuild descendants, so their facts are
--| stated through the walk (`dropLeftWalk`, `spineWalk`).
--|
--| P4, and the four passes together, are in `MergeProofs.sw`.

namespace Fmt.MeaningProofs
import Fmt (..)
import Fmt.Walk (..)
import Std (Bool, Eq, Fail, List, Nat, Option, Result, Text)
import Syntax (
  Attributes,
  BindingKind,
  Comments,
  Decl,
  DefKind,
  Expr,
  Fields,
  Group,
  Header,
  InfixKind,
  Param,
  Pattern,
  RuleSet,
  SourceFile,
  Steps,
  Tok,
  Word
)

-- P3 after a row: `dropLeft` removes only pairs that `forgetLeft` forgets.

theorem levelAtomic ∀ (expr: Expr) (high: 22 <= expr.level): expr.atomic = True := match expr with
  | CtorFields ctor record =>
    match record with
      | Record open base fields comma close =>
        match base with
          | None => cases
          | Some pair => cases
      | other => cases
  | other => cases

theorem negativeKept ∀ (membership recordRow: Bool) (expr: Expr)
    (negative: expr.negativeNumeral = True):
    keepsBrackets membership recordRow expr = True :=
  match expr with | Prefix _ (Atom Num _) | Prefix _ (Atom Float _) => cases

theorem enoughAbove ∀ (atomOnly: Bool) (floor more: Nat)
    (enough: atomOnly = True → 22 <= floor)
    (yes: atomOnly = True):
    22 <= Nat.max floor more :=
  arithmetic [enough yes, Nat.leMaxLeft floor more]

theorem enoughHead ∀ (floor: Nat) (yes: True = True): 22 <= Nat.max floor 22 := Nat.leMaxRight floor 22

-- The passes keep `meaning`: each pass's steps, as pure functions, keep
-- what `meaning`'s walk gives of the node they rewrite (`Keeps`), and the
-- traversal lemma (`applyKeeps`) does the rest.

def meaningPure: Pure := {
  expr = (expr => plainExpr (blankExpr expr)),
  pattern = (pattern => plainPattern (blankPattern pattern)),
  header = (header => plainHeader (blankHeader header)),
  decl = blankDecl,
  fields = (fields => { blankFields fields | trailingComma = False }),
  attributes = (attributes => { blankAttributes attributes | trailingComma = False }),
  ruleSet = (set => { blankRuleSet set | trailingComma = False })
}

def meaningAgrees: Agrees meaningSteps meaningPure := {
  expr = (z => byComputing),
  pattern = (z => byComputing),
  header = (z => byComputing),
  decl = (z => byComputing),
  fields = (z => byComputing),
  attributes = (z => byComputing),
  ruleSet = (z => byComputing)
}

def Pure.keep: Pure := {
  expr = (e => e),
  pattern = (p => p),
  header = (h => h),
  decl = (d => d),
  fields = (f => f),
  attributes = (a => a),
  ruleSet = (r => r)
}

-- P1.

def forallPure: Pure := { Pure.keep | header = withForall }

def forallAgrees: Agrees { Steps.keep | header = withForall } forallPure := {
  expr = (z => byComputing),
  pattern = (z => byComputing),
  header = (z => byComputing),
  decl = (z => byComputing),
  fields = (z => byComputing),
  attributes = (z => byComputing),
  ruleSet = (z => byComputing)
}

theorem forallWalk ∀ (header: Header): walkHeader meaningPure (withForall header) = walkHeader meaningPure header :=
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
      match kind, forallKeyword with
        | DefTheorem, None =>
          match explicit: params.any Group.explicit with
            | True => byComputing
            | False => byComputing
        | _, _ => cases kind, forallKeyword then byComputing

def forallKeeps: Keeps forallPure meaningPure := {
  expr = (z => byComputing),
  pattern = (z => byComputing),
  header = forallWalk,
  decl = (z => byComputing),
  fields = (z => byComputing),
  attributes = (z => byComputing),
  ruleSet = (z => byComputing)
}

--| P1 keeps `meaning`.
theorem forallKeepsFile ∀ (file: SourceFile): file.withForall.meaning = file.meaning :=
  rewrite applyKeeps file.withoutEnd
    { Steps.keep | header = withForall }
    meaningSteps
    forallPure
    meaningPure
    forallAgrees
    meaningAgrees
    forallKeeps

-- P2.

def commaSteps: Steps := { Steps.keep |
  expr = withoutCommaExpr,
  pattern = withoutCommaPattern,
  fields = (fields => { fields | trailingComma = False }),
  attributes = (attributes => { attributes | trailingComma = False }),
  ruleSet = (set => { set | trailingComma = False })
}

def commaPure: Pure := { Pure.keep |
  expr = withoutCommaExpr,
  pattern = withoutCommaPattern,
  fields = (fields => { fields | trailingComma = False }),
  attributes = (attributes => { attributes | trailingComma = False }),
  ruleSet = (set => { set | trailingComma = False })
}

def commaAgrees: Agrees commaSteps commaPure := {
  expr = (z => byComputing),
  pattern = (z => byComputing),
  header = (z => byComputing),
  decl = (z => byComputing),
  fields = (z => byComputing),
  attributes = (z => byComputing),
  ruleSet = (z => byComputing)
}

theorem commaExprWalk ∀ (expr: Expr): (withoutCommaExpr expr).walk meaningPure = expr.walk meaningPure := cases

theorem commaPatternWalk ∀ (pattern: Pattern):
    (withoutCommaPattern pattern).walk meaningPure = pattern.walk meaningPure :=
  match pattern with
    | PatternRecord fields | PatternCtorFields _ fields =>
      match fields with
        | { open, fields, trailingComma, rest, close } => byComputing
    | _ => cases

theorem commaFieldsWalk ∀ (fields: Fields):
    { fields | trailingComma = False }.walk meaningPure = fields.walk meaningPure :=
  match fields with | { open, fields, trailingComma, close } => byComputing

theorem commaRuleSetWalk ∀ (set: RuleSet):
    walkRuleSet meaningPure { set | trailingComma = False } = walkRuleSet meaningPure set :=
  match set with | { open, rules, trailingComma, close } => byComputing

theorem commaAttributesWalk ∀ (attributes: Attributes):
    { blankAttributes { attributes | trailingComma = False } | trailingComma = False }
      = { blankAttributes attributes | trailingComma = False } :=
  byComputing

def commaKeeps: Keeps commaPure meaningPure := {
  expr = commaExprWalk,
  pattern = commaPatternWalk,
  header = (z => byComputing),
  decl = (z => byComputing),
  fields = commaFieldsWalk,
  attributes = commaAttributesWalk,
  ruleSet = commaRuleSetWalk
}

--| P2 keeps `meaning`.
theorem commaKeepsFile ∀ (file: SourceFile): file.withoutTrailingCommas.meaning = file.meaning :=
  rewrite applyKeeps file.withoutEnd commaSteps meaningSteps commaPure meaningPure commaAgrees meaningAgrees commaKeeps

-- P3 after a row, through `meaning`'s walk: the walk keeps whether a form
-- is a negative numeral and whether it is atomic, so `dropLeft` still
-- drops only pairs `forgetLeft` forgets.

theorem negativeWalk ∀ (expr: Expr): (expr.walk meaningPure).negativeNumeral = expr.negativeNumeral := match expr with
  | Prefix operator operand =>
    match operand with
      | Atom kind word => cases
      | _ => cases
  | _ => cases

theorem atomicWalk ∀ (expr: Expr): (expr.walk meaningPure).atomic = expr.atomic := match expr with
  | CtorFields ctor record =>
    match record with
      | Record open base fields comma close =>
        match base with
          | None => byComputing
          | Some (value, bar) => byComputing
      | _ => cases
  | FieldAccess target dot field =>
    match target with
      | None => byComputing
      | Some value => byComputing
  | _ => cases

--| A pair `dropLeft` drops is one `forgetLeft` forgets, after the walk.
theorem parenWalkForgotten ∀ (floor: Nat) (membership recordRow atomOnly: Bool) (open: Word)
    (inner: Expr) (close left right: Word)
    (enough: atomOnly = True → 22 <= floor)
    (drops: (open.bare
      && close.bare
      && !holdsFunction inner
      && floor <= inner.level
      && !keepsBrackets membership recordRow inner)
      = True):
    forgetLeft atomOnly (Paren left (inner.walk meaningPure) right) = forgetLeft atomOnly (inner.walk meaningPure) :=
  match negative: inner.negativeNumeral with
    | True =>
      let keeps := negativeKept membership recordRow inner negative
      cases
    | False =>
      match atomOnly with
        | False => rewrite negativeWalk inner, negative
        | True =>
          match atomic: inner.atomic with
            | True => rewrite negativeWalk inner, negative, atomicWalk inner, atomic
            | False =>
              match within: floor <= inner.level with
                | False => cases
                | True =>
                  let high: 22 <= inner.level := arithmetic [enough byComputing, within]
                  let atomicAfterAll := levelAtomic inner high
                  cases

--| By induction along the left end.
theorem dropLeftWalk ∀ (floor: Nat) (membership recordRow atomOnly: Bool) (expr: Expr)
    (enough: atomOnly = True → 22 <= floor):
    forgetLeft atomOnly ((dropLeft floor membership recordRow expr).walk meaningPure)
      = forgetLeft atomOnly (expr.walk meaningPure) :=
  match expr with
    | Paren open inner close =>
      match drops: open.bare
        && close.bare
        && !holdsFunction inner
        && floor <= inner.level
        && !keepsBrackets membership recordRow inner with
        | False => byComputing
        | True =>
          rewrite parenWalkForgotten floor membership recordRow atomOnly open inner close open.blank close.blank enough
                  drops then
            dropLeftWalk floor membership recordRow atomOnly inner enough
    | Infix kind left operator right =>
      rewrite dropLeftWalk
        (Nat.max floor (leftNeeds kind operator.text))
        (membership || kind == InfixMembership)
        recordRow
        atomOnly
        left
        (enoughAbove atomOnly floor (leftNeeds kind operator.text) enough)
    | Chain first rest =>
      rewrite dropLeftWalk (Nat.max floor 8) membership recordRow atomOnly first (enoughAbove atomOnly floor 8 enough)
    | App head _ | FieldAccess (Some head) _ _ =>
      rewrite dropLeftWalk (Nat.max floor 22) membership recordRow True head (enoughHead floor)
    | _ => cases

theorem rowWalk ∀ (expr: Expr): (dropAfterRow expr).walk meaningPure = expr.walk meaningPure := match expr with
  | Effect row result => rewrite dropLeftWalk 0 False (rowReadsAsRecord row) False result (never => cases)
  | _ => cases

-- P3 around a binder's whole type, through `meaning`'s walk.

theorem stripWalk ∀ (expr: Expr):
    ((stripBinderType expr).walk meaningPure).unwrapped = (expr.walk meaningPure).unwrapped :=
  match expr with
    | Paren open inner close =>
      match bare: open.bare && close.bare with
        | True => stripWalk inner
        | False => rewrite stripWalk inner
    | _ => cases

theorem groupBindersWalk ∀ (group: Group):
    ((dropGroupParens group).walk meaningPure).blank.plainType = (group.walk meaningPure).blank.plainType :=
  match group with
    | { kind, implicit, open, attributes, auto, names, colon, annotation, default, close, bare } =>
      match strips: !implicit && colon.isSome && default.isNone && auto.isNone with
        | False => byComputing
        | True =>
          match annotation with
            | Some written => rewrite stripWalk written
            | None => byComputing

theorem groupsBindersWalk ∀ (groups: List Group):
    (blankGroups (walkGroups meaningPure (groups.map dropGroupParens))).map Group.plainType
      = (blankGroups (walkGroups meaningPure groups)).map Group.plainType :=
  match groups with
    | [] => byComputing
    | [group, ..rest] => rewrite groupBindersWalk group, groupsBindersWalk rest

theorem paramsBindersWalk ∀ (params: List Param):
    (blankParams (walkParams meaningPure (params.map dropParam))).map Param.plainType
      = (blankParams (walkParams meaningPure params)).map Param.plainType :=
  match params with
    | [] => byComputing
    | [NameParam _, ..rest] | [PatternParam _, ..rest] => rewrite paramsBindersWalk rest
    | [Grouped group, ..rest] => rewrite groupBindersWalk group, paramsBindersWalk rest
    | [TypedPattern open pattern colon annotation close, ..rest] => rewrite stripWalk annotation, paramsBindersWalk rest

--| The header's type, down its spine: every binder `spineBinders` reaches
--| has its type unwrapped by `meaning` too.
theorem spineWalk ∀ (expr: Expr): (spineBinders expr).walk meaningPure = expr.walk meaningPure := match expr with
  | FunctionType binder arrow result => rewrite groupBindersWalk binder, spineWalk result
  | Effect row result => rewrite spineWalk result
  | Infix kind left operator right => rewrite spineWalk left, spineWalk right
  | Binding kind keyword params arrow body =>
    match kind with
      | BindsLambda => rewrite paramsBindersWalk params, spineWalk body
      | BindsForall => rewrite paramsBindersWalk params, spineWalk body
      | BindsExists => rewrite paramsBindersWalk params, spineWalk body
  | Annotation open value colon annotation close => rewrite stripWalk annotation
  | App head arguments => rewrite spineWalk head, spineAllWalk arguments
  | Prefix operator operand => rewrite spineWalk operand
  | _ => cases

theorem spineAllWalk ∀ (exprs: List Expr): walkExprs meaningPure (spineAll exprs) = walkExprs meaningPure exprs :=
  match exprs with
    | [] => byComputing
    | [first, ..rest] => rewrite spineWalk first, spineAllWalk rest

theorem headerBindersWalk ∀ (header: Header):
    walkHeader meaningPure (dropBinderBrackets header) = walkHeader meaningPure header :=
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
      match kind, decreasingClause with
        | DefPlain, None => rewrite groupsBindersWalk params, spineWalk result
        | DefPlain, Some (word, measure) => rewrite groupsBindersWalk params, spineWalk result, spineWalk measure
        | DefTheorem, None => rewrite groupsBindersWalk params, spineWalk result
        | DefTheorem, Some (word, measure) => rewrite groupsBindersWalk params, spineWalk result, spineWalk measure
        | DefInstance, None => rewrite groupsBindersWalk params, spineWalk result
        | DefInstance, Some (word, measure) => rewrite groupsBindersWalk params, spineWalk result, spineWalk measure

def dropDeclBindersPure: Decl → Decl
  | Definition attributes header body => Definition attributes (dropBinderBrackets header) body
  | other => other

theorem declBindersAgree ∀ (decl: Decl): Fail.toResult (() => dropDeclBinders decl) = Ok (dropDeclBindersPure decl) :=
  cases

theorem declBindersWalk ∀ (decl: Decl): (dropDeclBindersPure decl).walk meaningPure = decl.walk meaningPure :=
  match decl with
    | Definition attributes header body => rewrite headerBindersWalk header
    | _ => cases

def bracketSteps: Steps := { Steps.keep | expr = dropAfterRow, decl = dropDeclBinders }

def bracketPure: Pure := { Pure.keep | expr = dropAfterRow, decl = dropDeclBindersPure }

def bracketAgrees: Agrees bracketSteps bracketPure := {
  expr = (z => byComputing),
  pattern = (z => byComputing),
  header = (z => byComputing),
  decl = declBindersAgree,
  fields = (z => byComputing),
  attributes = (z => byComputing),
  ruleSet = (z => byComputing)
}

def bracketKeeps: Keeps bracketPure meaningPure := {
  expr = rowWalk,
  pattern = (z => byComputing),
  header = (z => byComputing),
  decl = declBindersWalk,
  fields = (z => byComputing),
  attributes = (z => byComputing),
  ruleSet = (z => byComputing)
}

--| P3 keeps `meaning`.
theorem bracketKeepsFile ∀ (file: SourceFile): file.withoutSpareBrackets.meaning = file.meaning :=
  rewrite applyKeeps file.withoutEnd bracketSteps meaningSteps bracketPure meaningPure bracketAgrees meaningAgrees
      bracketKeeps

--| The first three passes keep `meaning`.
theorem firstThreeKeepMeaning ∀ (file: SourceFile):
    file.withForall.withoutTrailingCommas.withoutSpareBrackets.meaning = file.meaning :=
  rewrite bracketKeepsFile file.withForall.withoutTrailingCommas, commaKeepsFile file.withForall, forallKeepsFile file
