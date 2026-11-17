--| P4, merged parameter groups: its family (toy-plus-plus.md §3.2), from
--| the traversal's lemmas with a step that touches no expression
--| (`keepExpr`) and `declare` that merges a function's groups
--| (`Declaration.withMergedParameters`).
--|
--| What P4 needs of its own is about lists of groups: folding them keeps
--| the meaning (a merged group is what `plain` would split into), keeps
--| the parser's guarantees (each type and name is one of the originals'),
--| keeps every comment (the group that goes holds none), and finishes in
--| one run (nothing mergeable is left after the fold).

namespace Toy.Fmt.Proofs
import Toy.Syntax (..)
import Toy.Syntax.Proofs (..)
import Toy.Fmt (..)
import Std (Bool, DecEq, Eq, List, NonEmptyList, Nat, Option, Text)

-- The step touches no expression, so a traversal with it changes nothing.

theorem keepTraverse ∀ (expr: Expr) (position: Position): expr.traverse keepExpr position = expr :=
  keepInside expr position.bracketed

theorem keepInside ∀ (expr: Expr) (bracketed: Bool): expr.traverseInside keepExpr bracketed = expr := match expr with
  | Var _ _ => byComputing
  | NumberLiteral _ _ => byComputing
  | StringLiteral _ _ => byComputing
  | Bracketed _ inner _ => rewrite keepTraverse inner { bracketed = True, slot = Whole }
  | ListLiteral _ items _ _ => rewrite keepItems items
  | Call callee _ arguments _ _ => rewrite keepTraverse callee { bracketed, slot = PostfixSlot }, keepItems arguments
  | Field target _ _ _ => rewrite keepTraverse target { bracketed, slot = PostfixSlot }
  | Negate _ operand => rewrite keepTraverse operand { bracketed, slot = OperandSlot }
  | Binary operator _ left right =>
    rewrite keepTraverse left { bracketed, slot = LeftOf operator.level },
        keepTraverse right { bracketed, slot = RightOf operator.level }
  | If _ condition _ whenTrue _ whenFalse =>
    rewrite keepTraverse condition { bracketed, slot = Whole },
        keepBody whenTrue bracketed,
        keepBody whenFalse bracketed

theorem keepItems ∀ (items: List Expr): traverseItems keepExpr items = items := match items with
  | [] => byComputing
  | [value, ..rest] => rewrite keepTraverse value { bracketed = True, slot = Whole }, keepItems rest

theorem keepBody ∀ (body: Body) (bracketed: Bool): body.traverse keepExpr bracketed = body := match body with
  | { statements } => rewrite keepLines statements bracketed

theorem keepLines ∀ (lines: List (Spaced Statement)) (bracketed: Bool):
    traverseLines keepExpr bracketed lines = lines :=
  match lines with
    | [] => byComputing
    | [{ blankBefore, line }, ..rest] => rewrite keepStatement line bracketed, keepLines rest bracketed

theorem keepStatement ∀ (line: Statement) (bracketed: Bool): line.traverse keepExpr bracketed = line := match line with
  | Let _ _ _ _ body => rewrite keepBody body False
  | Bare value => rewrite keepTraverse value { bracketed, slot = Whole }
  | StatementNote _ => byComputing

theorem keepDeclaration ∀ (line: Declaration): line.traverseBody keepExpr = line := match line with
  | Function _ _ _ _ _ _ _ _ _ body => rewrite keepBody body False
  | Value _ _ _ _ body => rewrite keepBody body False
  | DeclarationNote _ => byComputing

--| The declarations with P4's `declare` at each: what `withMergedParameters`
--| does once the traversal's identity step is out of the way.
def declarationsMerged: List (Spaced Declaration) → List (Spaced Declaration)
  | [] => []
  | [{ blankBefore, line }, ..rest] => [{ blankBefore, line = line.withMergedParameters }, ..declarationsMerged rest]

theorem mergedDeclarations ∀ (lines: List (Spaced Declaration)):
    traverseDeclarations keepExpr (line => line.withMergedParameters) lines = declarationsMerged lines :=
  match lines with
    | [] => byComputing
    | [{ blankBefore, line }, ..rest] => rewrite keepDeclaration line, mergedDeclarations rest

--| P4 is `declare` alone at each declaration.
theorem mergedIsDeclarations ∀ (file: SourceFile):
    file.withMergedParameters = { declarations = declarationsMerged file.declarations } :=
  rewrite mergedDeclarations file.declarations

-- Types: a type's name is what `bare` keeps.

theorem typeBareName ∀ (annotation: TypeExpr): annotation.bare = TypeName annotation.baseName Comments.none :=
  match annotation with
    | TypeName _ _ => byComputing
    | TypeBracketed _ inner _ => typeBareName inner

theorem typePlainBare ∀ (annotation: TypeExpr): annotation.plain.bare = annotation.bare := match annotation with
  | TypeName _ _ => byComputing
  | TypeBracketed open inner close =>
    match none: open.isNone && close.isNone with
      | True => typePlainBare inner
      | False => rewrite typePlainBare inner

theorem isNoneEq ∀ (comments: Comments) (none: comments.isNone = True): comments = Comments.none :=
  match comments, none with | { above = [], after = None }, _ => byComputing

-- What a group that merges into the next one is.

--| A group merged into the next: a bare type with no comment on it or on
--| the `:`, and the next group's type is that name.
theorem mergesParts ∀ (names more: NonEmptyList Named) (colon colon2 comments: Comments)
    (name: Text) (annotation: TypeExpr)
    (merges: (Typed names colon (TypeName name comments)).mergesInto (Typed more colon2 annotation) = True):
    colon = Comments.none ∧ comments = Comments.none ∧ annotation.bare = TypeName name Comments.none :=
  let (colonNone, commentsNone, sameName) := merges.read
  (isNoneEq colon colonNone, isNoneEq comments commentsNone, rewrite typeBareName annotation, DecEq.sound sameName)

-- The meaning: `plain` splits a group into one group for each name, so a
-- group with the next one's names in front of it splits into the first
-- group's names, with its bare type, and then the next's.

theorem splitJoin ∀ (first: Named) (others: List Named) (x: Named) (ys: List Named) (colon: Comments)
    (annotation: TypeExpr) (name: Text)
    (bare: annotation.bare = TypeName name Comments.none):
    splitGroup first (others ++ [x, ..ys]) colon annotation
      = splitGroup first others Comments.none (TypeName name Comments.none) ++ splitGroup x ys colon annotation :=
  match others with
    | [] => rewrite bare
    | [next, ..rest] => rewrite bare, splitJoin next rest x ys colon annotation name bare

--| The merged group splits as the two groups did.
theorem mergedPlain ∀ (names more: NonEmptyList Named) (colon: Comments) (annotation: TypeExpr) (name: Text)
    (bare: annotation.bare = TypeName name Comments.none) (others: List ParameterGroup):
    plainGroups [Typed (joinNames names more) colon annotation, ..others]
      = plainGroups [Typed names Comments.none (TypeName name Comments.none), Typed more colon annotation, ..others] :=
  calc plainGroups [Typed (joinNames names more) colon annotation, ..others]
    _ = splitGroup names.head (names.tail ++ [more.head, ..more.tail]) colon annotation.plain ++ plainGroups others
    _ = (splitGroup names.head names.tail Comments.none (TypeName name Comments.none)
        ++ splitGroup more.head more.tail colon annotation.plain)
        ++ plainGroups others :=
      rewrite splitJoin names.head names.tail more.head more.tail colon annotation.plain name
        (rewrite typePlainBare annotation then bare)
    _ = splitGroup names.head names.tail Comments.none (TypeName name Comments.none)
        ++ (splitGroup more.head more.tail colon annotation.plain ++ plainGroups others) := List.appendAssoc _ _ _

--| Folding one group onto the rest keeps the meaning. Proof idea: by cases on
--| the two groups; where they merge, `mergesParts` says the first group's
--| `:` and type hold no comment and the next type's bare name is the
--| first's, which is what `mergedPlain` (through `splitJoin`) needs.
theorem mergeOntoPlain ∀ (group: ParameterGroup) (rest: List ParameterGroup):
    plainGroups (mergeOnto group rest) = plainGroups [group, ..rest] :=
  match group, rest with
    | Typed names colon (TypeName name comments), [Typed more colon2 annotation, ..others] =>
      match merges: (Typed names colon (TypeName name comments)).mergesInto (Typed more colon2 annotation) with
        | False => byComputing
        | True =>
          let (colonNone, commentsNone, bare) := mergesParts names more colon colon2 comments name annotation merges
          rewrite colonNone, commentsNone then mergedPlain names more colon2 annotation name bare others
    | _, _ => cases

theorem groupsMergePlain ∀ (groups: List ParameterGroup): plainGroups (mergeGroups groups) = plainGroups groups :=
  match groups with
    | [] => byComputing
    | [group, ..rest] =>
      calc plainGroups (mergeGroups [group, ..rest])
        _ = plainGroups [group, ..mergeGroups rest] := mergeOntoPlain group (mergeGroups rest)
        _ = plainGroups [group, ..rest] := rewrite groupsMergePlain rest

theorem declareMergePlain ∀ (line: Declaration): line.withMergedParameters.plain = line.plain := match line with
  | Function _ _ _ _ _ parameters _ _ _ _ => rewrite groupsMergePlain parameters
  | Value _ _ _ _ _ => byComputing
  | DeclarationNote _ => byComputing

theorem keepPlain: StepKeepsPlain keepExpr := position expr => byComputing

--| P4 keeps the meaning, on every tree: `plain` gives each name a group of
--| its own, with its type as a bare name.
theorem mergeKeepMeaning ∀ (file: SourceFile): file.withMergedParameters.meaning = file.meaning :=
  traverseKeepsMeaning keepExpr (line => line.withMergedParameters) keepPlain declareMergePlain file

-- The parser's guarantees: P4 keeps a group's names and its last type, so
-- each guarantee about the groups holds of the folded list.

--| A group put before others is never the end of the list: the result has a
--| first group.
theorem mergeOntoCons ∀ (group: ParameterGroup) (rest: List ParameterGroup):
    ∃ (first: ParameterGroup) (others: List ParameterGroup) => mergeOnto group rest = [first, ..others] :=
  match rest with
    | [] => (group, [], byComputing)
    | [next, ..others] =>
      match merges: group.mergesInto next with
        | True => (group.mergedWith next, others, byComputing)
        | False => (group, [next, ..others], byComputing)

--| The token before the closing bracket is the last group's last token,
--| which P4 keeps.
theorem mergeOntoEnds ∀ (open: Comments) (group: ParameterGroup) (rest: List ParameterGroup):
    groupsEndWithComment open (mergeOnto group rest) = groupsEndWithComment open [group, ..rest] :=
  match group, rest with
    | _, [] => byComputing
    | Untyped _, [_, .._] => byComputing
    | Typed _ _ (TypeBracketed _ _ _), [_, .._] => byComputing
    | Typed _ _ (TypeName _ _), [Untyped _, .._] => byComputing
    | Typed names colon (TypeName name comments), [Typed more colon2 annotation, ..others] =>
      match merges: (Typed names colon (TypeName name comments)).mergesInto (Typed more colon2 annotation) with
        | False => byComputing
        | True =>
          match others with
            | [] => byComputing
            | [_, .._] => byComputing

theorem groupsMergeEnds ∀ (open: Comments) (groups: List ParameterGroup):
    groupsEndWithComment open (mergeGroups groups) = groupsEndWithComment open groups :=
  match groups with
    | [] => byComputing
    | [group, ..rest] =>
      let folded: groupsEndWithComment open (mergeGroups [group, ..rest])
        = groupsEndWithComment open [group, ..mergeGroups rest] :=
        mergeOntoEnds open group (mergeGroups rest)
      match rest with
        | [] => folded
        | [next, ..others] =>
          let (first, more, eq) := mergeOntoCons next (mergeGroups others)
          let inner := groupsMergeEnds open [next, ..others]
          calc groupsEndWithComment open (mergeGroups [group, next, ..others])
            _ = groupsEndWithComment open [group, ..mergeGroups [next, ..others]] := folded
            _ = groupsEndWithComment open (mergeGroups [next, ..others]) := rewrite eq
            _ = groupsEndWithComment open [next, ..others] := inner
            _ = groupsEndWithComment open [group, next, ..others] := byComputing

theorem mergeOntoShaped ∀ (group: ParameterGroup) (rest: List ParameterGroup)
    (shaped: ShapedGroups [group, ..rest]):
    ShapedGroups (mergeOnto group rest) :=
  match group, rest, shaped with
    | _, [], shaped => shaped
    | Untyped _, [_, .._], shaped => shaped
    | Typed _ _ (TypeBracketed _ _ _), [_, .._], shaped => shaped
    | Typed _ _ (TypeName _ _), [Untyped _, .._], shaped => shaped
    | Typed names colon (TypeName name comments), [Typed more colon2 annotation, ..others], shaped =>
      match merges: (Typed names colon (TypeName name comments)).mergesInto (Typed more colon2 annotation) with
        | False => shaped
        | True => shaped.right

theorem groupsMergeShaped ∀ (groups: List ParameterGroup)
    (shaped: ShapedGroups groups):
    ShapedGroups (mergeGroups groups) :=
  match groups, shaped with
    | [], _ => byComputing
    | [group, ..rest], (groupShaped, restShaped) =>
      mergeOntoShaped group (mergeGroups rest) (groupShaped, groupsMergeShaped rest restShaped)

theorem namesLexicalAppend ∀ (front back: List Named)
    (frontLexical: LexicalNames front)
    (backLexical: LexicalNames back):
    LexicalNames (front ++ back) :=
  match front, frontLexical with
    | [], _ => backLexical
    | [named, ..rest], (namedLexical, restLexical) =>
      (namedLexical, namesLexicalAppend rest back restLexical backLexical)

--| Folding keeps the lexer's texts. Proof idea: by cases on the two groups;
--| a merged group's names are the first group's and the next group's, each
--| fine, and `namesLexicalAppend` joins the tails.
theorem mergeOntoLexical ∀ (group: ParameterGroup) (rest: List ParameterGroup)
    (lexical: LexicalParameters [group, ..rest]):
    LexicalParameters (mergeOnto group rest) :=
  match group, rest, lexical with
    | _, [], lexical => lexical
    | Untyped _, [_, .._], lexical => lexical
    | Typed _ _ (TypeBracketed _ _ _), [_, .._], lexical => lexical
    | Typed _ _ (TypeName _ _), [Untyped _, .._], lexical => lexical
    | Typed names colon (TypeName name comments), [Typed more colon2 annotation, ..others], (
        (head, tail, colonFine, nameFine),
        (moreHead, moreTail, colon2Fine, annotationFine),
        othersLexical
      ) =>
      match merges: (Typed names colon (TypeName name comments)).mergesInto (Typed more colon2 annotation) with
        | False => ((head, tail, colonFine, nameFine), (moreHead, moreTail, colon2Fine, annotationFine), othersLexical)
        | True => (
          (
            head,
            namesLexicalAppend names.tail [more.head, ..more.tail] tail (moreHead, moreTail),
            colon2Fine,
            annotationFine
          ),
          othersLexical
        )

theorem groupsMergeLexical ∀ (groups: List ParameterGroup)
    (lexical: LexicalParameters groups):
    LexicalParameters (mergeGroups groups) :=
  match groups, lexical with
    | [], _ => byComputing
    | [group, ..rest], (groupLexical, restLexical) =>
      mergeOntoLexical group (mergeGroups rest) (groupLexical, groupsMergeLexical rest restLexical)

theorem keepShaped: StepKeepsShaped keepExpr := position expr shaped => (shaped, (ends => ends))

theorem keepLexical: StepKeepsLexical keepExpr := position expr lexical => lexical

theorem keepHeaded: StepKeepsHeaded keepExpr := position expr headed => (headed, byComputing)

--| Only the parameter groups change, and the list's `)` stays settled
--| because the last token is the same.
theorem declareMergeParsed: DeclareKeepsParsed (line => line.withMergedParameters) := line shaped lexical headed =>
  match line, shaped, lexical with
    | Function _ _ _ _ open parameters _ close _ _, ((groupsShaped, settled), bodyShaped), (fnFine, isName, nameFine,
        takesFine, openFine, groupsLexical, closeFine, equalsFine, bodyLexical) => (
      ((groupsMergeShaped parameters groupsShaped, rewrite groupsMergeEnds open parameters then settled), bodyShaped),
      (
        fnFine,
        isName,
        nameFine,
        takesFine,
        openFine,
        groupsMergeLexical parameters groupsLexical,
        closeFine,
        equalsFine,
        bodyLexical
      ),
      headed
    )
    | Value _ _ _ _ _, shaped, lexical => (shaped, lexical, headed)
    | DeclarationNote _, shaped, lexical => (shaped, lexical, headed)

--| P4 keeps the parser's guarantees: only the parameters change, and the
--| types and names left are the originals'.
theorem mergeKeepParsed ∀ (file: SourceFile) (parsed: Parsed file): Parsed file.withMergedParameters :=
  traverseKeepsParsed keepExpr
    (line => line.withMergedParameters)
    keepShaped
    keepLexical
    keepHeaded
    declareMergeParsed
    file
    parsed

theorem keepCommas: StepKeepsCommas keepExpr := position expr none => none

theorem declareMergeCommas ∀ (line: Declaration)
    (none: NoTrailingCommasDeclaration line):
    NoTrailingCommasDeclaration line.withMergedParameters :=
  match line, none with
    | Function _ _ _ _ _ _ _ _ _ _, none => none
    | Value _ _ _ _ _, none => none
    | DeclarationNote _, none => none

--| P4 keeps P2's work: merging groups adds no trailing comma.
theorem mergeKeepCommas ∀ (file: SourceFile)
    (tidy: file.withoutTrailingCommas = file):
    file.withMergedParameters.withoutTrailingCommas = file.withMergedParameters :=
  commasFixed file.withMergedParameters
    (traverseKeepsCommas keepExpr
      (line => line.withMergedParameters)
      keepCommas
      declareMergeCommas
      file
      (commasTidyNone file tidy))

-- Done in one run: after the fold no group merges into the next, and the
-- fold leaves such a list alone.

--| No group of the list merges into the one after it.
def Unmergeable: List ParameterGroup → Prop
  | [] => True
  | [_] => True
  | [group, next, ..rest] => group.mergesInto next = False ∧ Unmergeable [next, ..rest]

--| A group that merges into `next` leaves the merged group merging into
--| what `next` did: it has `next`'s `:` and type.
theorem mergedMergesInto ∀ (names more: NonEmptyList Named) (colon colon2 comments: Comments) (name: Text)
    (annotation: TypeExpr) (after: ParameterGroup):
    (Typed (joinNames names more) colon2 annotation).mergesInto after
      = (Typed more colon2 annotation).mergesInto after :=
  match annotation, after with
    | TypeName _ _, Untyped _ => byComputing
    | TypeName _ _, Typed _ _ _ => byComputing
    | TypeBracketed _ _ _, Untyped _ => byComputing
    | TypeBracketed _ _ _, Typed _ _ _ => byComputing

--| Folding a group onto a list with nothing mergeable leaves nothing
--| mergeable. Proof idea: by cases on the two groups; a merged group has
--| the next group's `:` and type (`mergedMergesInto`), so it merges into
--| what the next group did not.
theorem mergeOntoUnmergeable ∀ (group: ParameterGroup) (rest: List ParameterGroup)
    (unmergeable: Unmergeable rest):
    Unmergeable (mergeOnto group rest) :=
  match group, rest, unmergeable with
    | _, [], _ => byComputing
    | Untyped _, [next, ..others], unmergeable => (byComputing, unmergeable)
    | Typed _ _ (TypeBracketed _ _ _), [next, ..others], unmergeable => (byComputing, unmergeable)
    | Typed _ _ (TypeName _ _), [Untyped _, ..others], unmergeable => (byComputing, unmergeable)
    | Typed names colon (TypeName name comments), [Typed more colon2 annotation, ..others], unmergeable =>
      match merges: (Typed names colon (TypeName name comments)).mergesInto (Typed more colon2 annotation) with
        | False => (merges, unmergeable)
        | True =>
          match others with
            | [] => byComputing
            | [after, ..afters] => (
              rewrite mergedMergesInto names more colon colon2 comments name annotation after then unmergeable.left,
              unmergeable.right
            )

theorem groupsMergeUnmergeable ∀ (groups: List ParameterGroup): Unmergeable (mergeGroups groups) := match groups with
  | [] => byComputing
  | [group, ..rest] => mergeOntoUnmergeable group (mergeGroups rest) (groupsMergeUnmergeable rest)

theorem unmergeableTail ∀ (group: ParameterGroup) (rest: List ParameterGroup)
    (unmergeable: Unmergeable [group, ..rest]):
    Unmergeable rest :=
  match rest with
    | [] => byComputing
    | [next, ..others] => unmergeable.right

theorem mergeOntoFixed ∀ (group: ParameterGroup) (rest: List ParameterGroup)
    (unmergeable: Unmergeable [group, ..rest]):
    mergeOnto group rest = [group, ..rest] :=
  match rest with
    | [] => byComputing
    | [next, ..others] => rewrite unmergeable.left

theorem groupsMergeFixed ∀ (groups: List ParameterGroup)
    (unmergeable: Unmergeable groups):
    mergeGroups groups = groups :=
  match groups with
    | [] => byComputing
    | [group, ..rest] =>
      let restFixed := groupsMergeFixed rest (unmergeableTail group rest unmergeable)
      rewrite restFixed then mergeOntoFixed group rest unmergeable

--| The fold finishes in one run: its result has nothing left to merge.
theorem groupsMergeTwice ∀ (groups: List ParameterGroup): mergeGroups (mergeGroups groups) = mergeGroups groups :=
  groupsMergeFixed (mergeGroups groups) (groupsMergeUnmergeable groups)

theorem declareMergeSettles: DeclareSettles keepExpr (line => line.withMergedParameters) := (
  (line =>
    match line with
      | Function _ _ _ _ _ _ _ _ _ _ => byComputing
      | Value _ _ _ _ _ => byComputing
      | DeclarationNote _ => byComputing),
  (line =>
    match line with
      | Function _ _ _ _ _ parameters _ _ _ _ => rewrite groupsMergeTwice parameters
      | Value _ _ _ _ _ => byComputing
      | DeclarationNote _ => byComputing)
)

--| Every node is done: the step changes nothing, so there is nothing to
--| reach.
def EveryNode (position: Position) (expr: Expr): Prop := True

theorem keepFixes: StepFixes keepExpr EveryNode := position expr isDone => byComputing

theorem keepReaches: StepReaches keepExpr EveryNode := position expr inside => (byComputing, inside)

--| P4 finishes in one run: the traversal changes no expression, and the
--| fold leaves its own result alone (`groupsMergeTwice`).
theorem mergeIdempotent ∀ (file: SourceFile):
    file.withMergedParameters.withMergedParameters = file.withMergedParameters :=
  traverseIdempotent keepExpr
    (line => line.withMergedParameters)
    EveryNode
    keepFixes
    keepReaches
    declareMergeSettles
    file

-- P4 keeps P1's work: the fold never empties a list or makes one.

theorem takesForMerge ∀ (takes: Option Comments) (parameters: List ParameterGroup):
    takesFor takes (mergeGroups parameters) = takesFor takes parameters :=
  match parameters with
    | [] => byComputing
    | [group, ..rest] =>
      let (first, others, eq) := mergeOntoCons group (mergeGroups rest)
      rewrite eq

theorem declarationTakesMerge ∀ (line: Declaration):
    line.withMergedParameters.withTakes = line.withTakes.withMergedParameters :=
  match line with
    | Function _ _ _ takes _ parameters _ _ _ _ => rewrite takesForMerge takes parameters
    | Value _ _ _ _ _ => byComputing
    | DeclarationNote _ => byComputing

theorem declarationsTakesMerge ∀ (lines: List (Spaced Declaration)):
    declarationsWithTakes (declarationsMerged lines) = declarationsMerged (declarationsWithTakes lines) :=
  match lines with
    | [] => byComputing
    | [{ blankBefore, line }, ..rest] => rewrite declarationTakesMerge line, declarationsTakesMerge rest

--| P1 and P4 commute: the fold keeps whether a function has parameters.
theorem mergeTakesCommute ∀ (file: SourceFile):
    file.withMergedParameters.withTakes = file.withTakes.withMergedParameters :=
  rewrite mergedIsDeclarations file, mergedIsDeclarations file.withTakes, declarationsTakesMerge file.declarations

--| P4 keeps P1's work.
theorem mergeKeepTakes ∀ (file: SourceFile)
    (tidy: file.withTakes = file):
    file.withMergedParameters.withTakes = file.withMergedParameters :=
  rewrite mergeTakesCommute file, tidy

-- P4 keeps P3's work: the types left are the originals'.

def declarationGroups: Declaration → List ParameterGroup
  | Function _ _ _ _ _ parameters _ _ _ _ => parameters
  | _ => []

def declarationBody: Declaration → Body
  | Function _ _ _ _ _ _ _ _ _ body => body
  | Value _ _ _ _ body => body
  | DeclarationNote _ => { statements = [] }

--| A group with `names` in place of its own, if it is typed.
def renamed (names: NonEmptyList Named): ParameterGroup → ParameterGroup
  | Typed _ colon annotation => Typed names colon annotation
  | other => other

--| Folding keeps P3's work. Proof idea: by cases on the two groups; a merged
--| group has the next group's type, which P3 had left alone, and the names
--| are not touched by P3.
theorem mergeOntoSpare ∀ (group: ParameterGroup) (rest: List ParameterGroup)
    (kept: groupsWithoutSpareBrackets [group, ..rest] = [group, ..rest]):
    groupsWithoutSpareBrackets (mergeOnto group rest) = mergeOnto group rest :=
  let groupKept := List.consInjectiveHead _ _ _ _ kept
  let restKept := Eq.cong (.drop 1) kept
  match group, rest with
    | _, [] => rewrite groupKept
    | Untyped _, [next, ..others] =>
      rewrite groupKept, List.consInjectiveHead _ _ _ _ restKept, Eq.cong (.drop 1) restKept
    | Typed _ _ (TypeBracketed _ _ _), [next, ..others] =>
      rewrite groupKept, List.consInjectiveHead _ _ _ _ restKept, Eq.cong (.drop 1) restKept
    | Typed _ _ (TypeName _ _), [Untyped _, ..others] =>
      rewrite groupKept, List.consInjectiveHead _ _ _ _ restKept, Eq.cong (.drop 1) restKept
    | Typed names colon (TypeName name comments), [Typed more colon2 annotation, ..others] =>
      let nextKept := List.consInjectiveHead _ _ _ _ restKept
      let othersKept := Eq.cong (.drop 1) restKept
      match merges: (Typed names colon (TypeName name comments)).mergesInto (Typed more colon2 annotation) with
        | False => rewrite groupKept, nextKept, othersKept
        | True => rewrite Eq.cong (renamed (joinNames names more)) nextKept, othersKept

theorem groupsMergeSpare ∀ (groups: List ParameterGroup)
    (kept: groupsWithoutSpareBrackets groups = groups):
    groupsWithoutSpareBrackets (mergeGroups groups) = mergeGroups groups :=
  match groups with
    | [] => byComputing
    | [group, ..rest] =>
      let restKept := groupsMergeSpare rest (Eq.cong (.drop 1) kept)
      let ahead: groupsWithoutSpareBrackets [group, ..mergeGroups rest] = [group, ..mergeGroups rest] :=
        rewrite List.consInjectiveHead _ _ _ _ kept, restKept
      mergeOntoSpare group (mergeGroups rest) ahead

theorem declarationMergeBrackets ∀ (line: Declaration)
    (kept: (line.traverseBody dropPair).withoutSpareTypeBrackets = line):
    (line.withMergedParameters.traverseBody dropPair).withoutSpareTypeBrackets = line.withMergedParameters :=
  match line with
    | Function _ _ _ _ _ parameters _ _ _ _ =>
      rewrite groupsMergeSpare parameters (Eq.cong declarationGroups kept), Eq.cong declarationBody kept
    | Value _ _ _ _ _ => kept
    | DeclarationNote _ => byComputing

theorem declarationsMergeBrackets ∀ (lines: List (Spaced Declaration))
    (kept: traverseDeclarations dropPair (line => line.withoutSpareTypeBrackets) lines = lines):
    traverseDeclarations dropPair (line => line.withoutSpareTypeBrackets) (declarationsMerged lines)
      = declarationsMerged lines :=
  match lines with
    | [] => byComputing
    | [{ blankBefore, line }, ..rest] =>
      let lineKept := Eq.cong (spaced => spaced.line) (List.consInjectiveHead _ _ _ _ kept)
      rewrite declarationMergeBrackets line lineKept, declarationsMergeBrackets rest (Eq.cong (.drop 1) kept)

--| P4 keeps P3's work: the types it leaves are the types P3 left.
theorem mergeKeepBrackets ∀ (file: SourceFile)
    (tidy: file.withoutSpareBrackets = file):
    file.withMergedParameters.withoutSpareBrackets = file.withMergedParameters :=
  rewrite mergedIsDeclarations file, declarationsMergeBrackets file.declarations (Eq.cong (.declarations) tidy)
