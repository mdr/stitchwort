--| Slice 1's read-back over any number of lines (SW-4121): a declaration whose items keep the line rule `Fmt.hangs`
--| parses back to the definition they spell (`readsBackHung`). The items are the group's own (`isItems`): the parser's
--| line test reads each item's bracket depth.
--|
--| `fullHung` is proved here from `fullHungStep` by induction on the depth; the rungs' lemmas are in
--| `Syntax.ReadBackHungAtoms` to `Syntax.ReadBackHungFull`.

namespace Syntax.ReadBackHungTop
import Std (Bool, Eq, List, Nat, Option, Parse, Result, Text, Void)
import Syntax (..)
import Fmt (..)
import Syntax.ReadBackProofs (..)
import Syntax.ReadBackRuns (..)
import Syntax.ReadBackRuns (plainHeader)
import Syntax.ReadBackTree (..)
import Syntax.ReadBackEnds (..)
import Syntax.ReadBackLine (..)
import Syntax.AutoPlaced (..)
import Syntax.ReadBackHung (..)
import Syntax.ReadBackHungDeep (hungDeep)
import Syntax.ReadBackHungAtomsLemmas (deepRest)
import Syntax.ReadBackHungFrame (speltHangs)
import Syntax.ReadBackHungFull (fullHungStep)

-- The full expression, at every depth.

--| `fullHung` at every depth below `limit`, by induction on `limit`.
theorem fullHungUpTo ∀ (limit depth: Nat) (below: depth < limit): FullHungAt depth := match limit with
  | Succ smaller => fullHungStep depth (inside less => fullHungUpTo smaller inside (arithmetic [below, less]))

--| What `expr` reads, on any lines: a spelt expression at the start of a type, a value or a bracket's item
--| (`state.start`), or after `->` (`state.glue`), whose leaves and what follows keep the line rule. Inline where its
--| first item starts no block; else a one-line block at that item's column.
theorem fullHung ∀ (modes: Modes)
    (quiet: QuietModes modes)
    (expr: Expr) (read rest: List Item) (depth: Nat) (state: HangState)
    (deep: expr.nest <= depth)
    (spelt: Spelt expr read)
    (free: expr.autoPlaced True = True)
    (lineRead: lineAll read = True)
    (lineRest: lineAll rest = True)
    (placed: state.start = True ∨ state.glue = True)
    (bound: bounds modes state = True)
    (hung: hangsFrom state (leavesOf (read ++ rest)) = True)
    (deepItems: deepAll (read ++ rest) = True)
    (ends: endsHere rest = True):
    FullReads (TreeN depth) modes read rest expr :=
  fullHungUpTo
    (Succ depth)
    depth
    (arithmetic [])
    modes
    expr
    read
    rest
    state
    quiet
    deep
    spelt
    free
    lineRead
    lineRest
    placed
    bound
    hung
    deepItems
    ends

-- The header.

--| The line rule's state at the start of a type or a value: after `:` or `:=`, outside brackets.
def HangState.atTop: HangState := { blocks = [], top = None, start = True, glue = False }

--| A group's leaves are its items'.
theorem leavesItems ∀ (group: List Leaf): leavesOf (items group) = group :=
  rewrite itemsStart group then placeItemsLeaves ItemsAt.start group

--| The line rule's state after a definition's name, outside brackets.
def HangState.afterName: HangState := { blocks = [], top = None, start = False, glue = False }

--| The line rule steps over a definition's name to `afterName`, or refuses it.
theorem nameStep ∀ (name: Leaf)
    (isLower: name.token.kind = Lower ∨ name.token.kind = Upper):
    HangState.initial.step name = None ∨ HangState.initial.step name = Some HangState.afterName :=
  match name with
    | { token = { kind, text, column, lineStart }, trivia } =>
      match isLower with
        | Inl lower => rewrite lower then cases
        | Inr upper => rewrite upper then cases

--| The line rule steps over the `:` after the name to the type's start, or refuses it.
theorem colonStep ∀ (colon: Leaf)
    (isColon: colon.token.kind = Colon):
    HangState.afterName.step colon = None ∨ HangState.afterName.step colon = Some HangState.atTop :=
  match colon with | { token = { kind, text, column, lineStart }, trivia } => rewrite isColon then cases

--| A `:=` outside brackets, after no `->`, steps to the value's start wherever it stands.
theorem colonEqStep ∀ (state: HangState) (colonEq: Leaf)
    (isColonEq: colonEq.token.kind = ColonEq)
    (outside: state.blocks = [])
    (unglued: state.glue = False):
    state.step colonEq = Some HangState.atTop :=
  match state with | { blocks, top, start, glue } => rewrite outside, unglued, isColonEq

--| After a definition's name and `:`, the line rule is at the type's start.
theorem headerHung ∀ (name colon: Leaf) (rest: List Leaf)
    (isLower: name.token.kind = Lower ∨ name.token.kind = Upper)
    (isColon: colon.token.kind = Colon)
    (hung: hangsFrom HangState.initial [name, colon, ..rest] = True):
    hangsFrom HangState.atTop rest = True :=
  match afterName: HangState.initial.step name with
    | Some next =>
      let isNext: next = HangState.afterName := match nameStep name isLower with
        | Inl none => (Option.someNotNone next (Eq.trans afterName.flipped none)).impossible
        | Inr some => Option.someInjective (Eq.trans afterName.flipped some)
      let fromName: hangsFrom HangState.afterName [colon, ..rest] = True := rewrite <- isNext then hung
      match afterColon: HangState.afterName.step colon with
        | Some atColon =>
          let isTop: atColon = HangState.atTop := match colonStep colon isColon with
            | Inl none => (Option.someNotNone atColon (Eq.trans afterColon.flipped none)).impossible
            | Inr some => Option.someInjective (Eq.trans afterColon.flipped some)
          rewrite <- isTop then fromName

--| A `:=` outside brackets and after no `->` puts the line rule at the value's start.
theorem colonEqHung ∀ (state: HangState) (colonEq: Leaf) (rest: List Leaf)
    (isColonEq: colonEq.token.kind = ColonEq)
    (outside: state.blocks = [])
    (unglued: state.glue = False)
    (hung: hangsFrom state [colonEq, ..rest] = True):
    hangsFrom HangState.atTop rest = True :=
  match stepped: state.step colonEq with
    | Some next =>
      let isTop: next = HangState.atTop :=
        Option.someInjective (Eq.trans stepped.flipped (colonEqStep state colonEq isColonEq outside unglued))
      rewrite <- isTop then hung

-- The declaration.

--| The read-back of a declaration on any lines: `def name: A := b`, with `A` and `b` spelt by the items between `:`
--| and `:=` and after `:=`, no list at a full expression's start in either starting with an `auto` call
--| (`autoPlaced`), and the group's leaves keeping the line rule, parses as `parseGroups` runs it to that definition,
--| the words being the items'.
--|
--| Proof idea: `declarationTree`, with the type and the value as `fullHung` trees under the start's and the body's
--| modes, which have no line limit. The line rule's state at the type's start is the header's (`headerHung`); the
--| state after the type is the one its first leaf entered (`speltHangs`), outside brackets, so the `:=` puts it at
--| the value's start (`colonEqHung`). Every closer and comma is inside a bracket (`hungDeep`).
theorem readsBackHung ∀ (seen: Seen) (group: List Leaf) (keyword name colon colonEq: Item)
    (typeRead valueRead: List Item) (result value: Expr)
    (isItems: items group = [keyword, name, colon, ..typeRead ++ [colonEq, ..valueRead]])
    (hung: hangs group = True)
    (isDef: keyword.kind = KwDef)
    (isLower: name.kind = Lower ∨ name.kind = Upper)
    (isColon: colon.kind = Colon)
    (isColonEq: colonEq.kind = ColonEq)
    (typeSpelt: Spelt result typeRead)
    (valueSpelt: Spelt value valueRead)
    (typeLine: lineAll typeRead = True)
    (valueLine: lineAll valueRead = True)
    (typePlaced: result.autoPlaced True = True)
    (valuePlaced: value.autoPlaced True = True):
    Parse.run (items group) (() =>
      let decl := declaration seen
      decl)
      = Ok (Definition [] (plainHeader keyword name colon result) (Assigned colonEq.leaf.word.comments value)) :=
  let startQuiet: QuietModes Modes.start := { noGuard = byComputing, noCalc = byComputing, noRule = byComputing }
  let body := { Modes.start | recover = True }
  let bodyQuiet: QuietModes body := { noGuard = byComputing, noCalc = byComputing, noRule = byComputing }
  let after := [colonEq, ..valueRead]
  let lineAfter: lineAll after = True := rewrite isColonEq, valueLine
  let hungItems: hangs (leavesOf [keyword, name, colon, ..typeRead ++ after]) = True :=
    rewrite <- isItems, leavesItems group then hung
  let fromColon: hangsFrom HangState.atTop (leavesOf (typeRead ++ after)) = True :=
    headerHung name.leaf colon.leaf
      (leavesOf (typeRead ++ after))
      isLower
      isColon
      (Bool.andRight (Bool.andRight hungItems))
  let deepGroup: deepAll [keyword, name, colon, ..typeRead ++ after] = True :=
    rewrite <- isItems then hungDeep group hung
  let deepType: deepAll (typeRead ++ after) = True := Bool.andRight (Bool.andRight (Bool.andRight deepGroup))
  let deepValue: deepAll (valueRead ++ []) = True :=
    rewrite List.appendNil valueRead then Bool.andRight (deepRest typeRead after deepType)
  let (first, more, isType, starts) := speltStarts result typeRead typeSpelt
  let typeLeaves: hangsAfter (HangState.atTop.after (leavesOf typeRead)) (leavesOf after) = True :=
    rewrite <- hangsFromAppend HangState.atTop (leavesOf typeRead) (leavesOf after),
        <- List.mapAppend typeRead after (item => item.leaf) then
      fromColon
  let valueHung: hangsFrom HangState.atTop (leavesOf (valueRead ++ [])) = True :=
    match typed: HangState.atTop.after (leavesOf typeRead) with
      | Some next =>
        let isNext: next = HangState.atTop.entered first.leaf :=
          speltHangs result first more HangState.atTop next
            (rewrite <- isType then typeSpelt)
            (rewrite <- isType then typed)
        let fromNext: hangsFrom next (leavesOf after) = True := typeLeaves
        rewrite List.appendNil valueRead then
          colonEqHung next colonEq.leaf (leavesOf valueRead) isColonEq (rewrite isNext) (rewrite isNext) fromNext
  let allowed: allowBraceOn Modes.start (typeRead ++ after) = Modes.start := rewrite isType
  let noRow: rowOn
    (isSome LBrace (peekIn (allowBraceOn Modes.start (typeRead ++ after)) 0 (typeRead ++ after)))
    (typeRead ++ after)
    = False :=
    rewrite allowed, isType, peekFirst Modes.start first (more ++ after) byComputing, startNotBrace first.kind starts
  let typeTree: Tree { modes = allowBraceOn Modes.start (typeRead ++ after), level = LevelFull } typeRead after
      result :=
    rewrite allowed then
      (
        Succ result.nest,
        fullHung Modes.start startQuiet result typeRead after result.nest HangState.atTop
          (arithmetic [])
          typeSpelt
          typePlaced
          typeLine
          lineAfter
          (Inl byComputing)
          byComputing
          fromColon
          deepType
          (rewrite isColonEq)
      )
  let valueTree: Tree { modes = body, level = LevelFull } valueRead [] value := (
    Succ value.nest,
    fullHung body bodyQuiet value valueRead [] value.nest HangState.atTop
      (arithmetic [])
      valueSpelt
      valuePlaced
      valueLine
      byComputing
      (Inl byComputing)
      byComputing
      valueHung
      deepValue
      byComputing
  )
  rewrite isItems then
    declarationTree seen keyword name colon colonEq typeRead valueRead result value {
      isDef,
      isLower,
      isColon,
      isColonEq,
      typeReads = (noRow, typeTree),
      valueTree
    }

-- Witnesses: the lexer's own items, over several lines.

--| The leaves the lexer gives a source, none if it doesn't lex.
def lexedLeaves (source: Text): List Leaf := match lex source with
  | Ok lexed => lexed.leaves
  | Err _ => []

--| The item at `index` of a source's lexed items.
def hungAt (source: Text) (index: Nat): Item := match (items (lexedLeaves source)).drop index with
  | [item, .._] => item
  | [] => wordItem Lower "x" 0

--| A list broken after its opener.
def listSource: Text := "def d: A := [\n  a, b]\n"

def listAt (index: Nat): Item := hungAt listSource index

def listValue: Expr :=
  ListOf
    (listAt 5).leaf.word
    [Atom Lower (listAt 6).leaf.word, Atom Lower (listAt 8).leaf.word]
    False
    (listAt 9).leaf.word

--| `def d: A := [⏎  a, b]`: `readsBackHung`'s hypotheses hold of the lexer's items, `a` starting the second line.
theorem readsBackHungListExample: Parse.run (items (lexedLeaves listSource)) (() =>
      let decl := declaration Seen.start
      decl)
      = Ok
        (Definition []
          (plainHeader (listAt 0) (listAt 1) (listAt 2) (Atom Upper (listAt 3).leaf.word))
          (Assigned (listAt 4).leaf.word.comments listValue)) :=
  readsBackHung Seen.start
    (lexedLeaves listSource)
    (listAt 0)
    (listAt 1)
    (listAt 2)
    (listAt 4)
    [listAt 3]
    [listAt 5, listAt 6, listAt 7, listAt 8, listAt 9]
    (Atom Upper (listAt 3).leaf.word)
    listValue
    byComputing
    byComputing
    byComputing
    (Inl byComputing)
    byComputing
    byComputing
    (listAt 3, byComputing, byComputing, byComputing, byComputing)
    (
      listAt 5,
      [listAt 6],
      [(listAt 7, [listAt 8], Atom Lower (listAt 8).leaf.word)],
      listAt 9,
      byComputing,
      byComputing,
      byComputing,
      byComputing,
      byComputing,
      byComputing,
      (listAt 6, byComputing, byComputing, byComputing, byComputing),
      (
        listAt 7,
        [listAt 8],
        [],
        byComputing,
        byComputing,
        (listAt 8, byComputing, byComputing, byComputing, byComputing),
        byComputing
      )
    )
    byComputing
    byComputing
    byComputing
    byComputing

--| A sign in brackets with a comment after it, its operand on the next line (D3686).
def signSource: Text := "def d: A := (- -- c\n  1)\n"

def signAt (index: Nat): Item := hungAt signSource index

def signValue: Expr :=
  Paren (signAt 5).leaf.word (Prefix (signAt 6).leaf.word (Atom Num (signAt 7).leaf.word)) (signAt 8).leaf.word

--| `def d: A := (- -- c⏎  1)`: `readsBackHung`'s hypotheses hold of the lexer's items, a comment inside the bracket
--| putting the operand on a line of its own.
theorem readsBackHungSignExample: Parse.run (items (lexedLeaves signSource)) (() =>
      let decl := declaration Seen.start
      decl)
      = Ok
        (Definition []
          (plainHeader (signAt 0) (signAt 1) (signAt 2) (Atom Upper (signAt 3).leaf.word))
          (Assigned (signAt 4).leaf.word.comments signValue)) :=
  readsBackHung Seen.start
    (lexedLeaves signSource)
    (signAt 0)
    (signAt 1)
    (signAt 2)
    (signAt 4)
    [signAt 3]
    [signAt 5, signAt 6, signAt 7, signAt 8]
    (Atom Upper (signAt 3).leaf.word)
    signValue
    byComputing
    byComputing
    byComputing
    (Inl byComputing)
    byComputing
    byComputing
    (signAt 3, byComputing, byComputing, byComputing, byComputing)
    (
      signAt 5,
      [signAt 6, signAt 7],
      signAt 8,
      byComputing,
      byComputing,
      byComputing,
      byComputing,
      byComputing,
      (
        signAt 6,
        [signAt 7],
        byComputing,
        byComputing,
        byComputing,
        (_ => byComputing),
        byComputing,
        (signAt 7, byComputing, byComputing, byComputing, byComputing)
      )
    )
    byComputing
    byComputing
    byComputing
    byComputing

--| A type on a line of its own, and `:=` at the type's column on the next (O5 of SW-4121).
def typeSource: Text := "def d:\n  A\n  := b\n"

def typeAt (index: Nat): Item := hungAt typeSource index

--| `def d:⏎  A⏎  := b`: `readsBackHung`'s hypotheses hold of the lexer's items, the `:=` starting a line at the
--| type's column.
theorem readsBackHungTypeExample: Parse.run (items (lexedLeaves typeSource)) (() =>
      let decl := declaration Seen.start
      decl)
      = Ok
        (Definition []
          (plainHeader (typeAt 0) (typeAt 1) (typeAt 2) (Atom Upper (typeAt 3).leaf.word))
          (Assigned (typeAt 4).leaf.word.comments (Atom Lower (typeAt 5).leaf.word))) :=
  readsBackHung Seen.start
    (lexedLeaves typeSource)
    (typeAt 0)
    (typeAt 1)
    (typeAt 2)
    (typeAt 4)
    [typeAt 3]
    [typeAt 5]
    (Atom Upper (typeAt 3).leaf.word)
    (Atom Lower (typeAt 5).leaf.word)
    byComputing
    byComputing
    byComputing
    (Inl byComputing)
    byComputing
    byComputing
    (typeAt 3, byComputing, byComputing, byComputing, byComputing)
    (typeAt 5, byComputing, byComputing, byComputing, byComputing)
    byComputing
    byComputing
    byComputing
    byComputing
