--| Slice 1's read-back (docs/proposals/self-hosted-fmt-s1-sketch.md §2, ticket 17): leaves that spell a tree and
--| `hangs` parse back to it. This file starts with the block lemmas the rest stands on: where the next line doesn't
--| start at a block's column, `block` reads one line and `blockLines` doesn't go round (`runsBlockOneLine`).

namespace Syntax.ReadBackProofs
import Std (Bool, DecEq, Eq, List, Nat, Option, Parse, Text)
import Syntax (..)
import Fmt (..)

-- Blocks.

--| Whether the next item takes a block at `column` round again (`blockLines`' test): it starts a line at that column
--| and doesn't end blocks.
def continuesAt (column: Nat): List Item → Bool
  | [next, .._] => next.leaf.token.lineStart && next.leaf.token.column == column && !endsBlocks next.kind
  | [] => False

--| The modes `blockLines` reads a line with, allowing `allow` (the index of the line's first item, `nextIndex`), the
--| line being of `kind`.
def lineModes (modes: Modes) (column: Nat) (many: Bool) (allow: Option Nat) (kind: LineKind): Modes :=
  { { modes | allow } | lines = [{ column, many, kind }, ..modes.lines] }

theorem andFalseRight ∀ (a b c: Bool) (no: c = False): (a && b && c) = False := match a, b with
  | True, True => no
  | True, False => byComputing
  | False, _ => byComputing

--| The modes `block` reads its lines with.
def blockModes (modes: Modes) (column: Nat) (many: Bool): Modes :=
  if many then { modes | limit = Some column, letValue = None } else { modes | limit = Some column }

-- Blocks, run: the completeness half, what the read-back builds on.

theorem runsOffset ∀ (state: Parse.State Item) (rest: List Item):
    Parse.RunsFrom state (() => offset()) [] rest state.at.offset :=
  Parse.runsFromMark state (here => here.offset) [] rest state.at.offset (Parse.runsPure state.at.offset rest state)

theorem runsLeft ∀ (state: Parse.State Item) (rest: List Item):
    Parse.RunsFrom state (() => left()) [] rest state.at.rest :=
  Parse.runsFromMark state (here => here.rest) [] rest state.at.rest (Parse.runsPure state.at.rest rest state)

--| `blockLines` runs one round: from `state`, where the line's statement runs reading `read`, and what follows it
--| doesn't continue the block.
--|
--| Proof idea: each step that reads nothing runs from any state, the statement from where the round started, and
--| `ends` makes the test for another round false.
theorem runsBlockLinesOneLine ∀ (more: Nat) (self: Goal → {Parse Item} Expr) (modes: Modes) (column: Nat) (many: Bool)
    (found: List Statement) (state: Parse.State Item) (read rest: List Item) (first: Statement)
    (line: ∀ (kind: LineKind) (middle: Parse.State Item) => middle.at.offset = state.at.offset
      → Parse.RunsFrom middle
        (() => statement self (lineModes modes column many (nextIndex (read ++ rest)) kind))
        read
        rest
        first)
    (ends: continuesAt column rest = False):
    Parse.RunsFrom state (() => blockLines (Succ more) self modes column many found) read rest [first, ..found] :=
  Parse.runsFromBindAt state
    (() => offset()) _
    []
    read
    read
    rest
    state.at.offset _
    byComputing
    (runsOffset state (read ++ rest))
    (middle restAt0 _ offset1 =>
      Parse.runsFromBindAt middle
        (() => left()) _
        []
        read
        read
        rest
        middle.at.rest _
        byComputing
        (runsLeft middle (read ++ rest))
        (middle1 _ _ offset2 =>
          rewrite restAt0 then
            Parse.runsFromMark middle1
              (here =>
                blockKind more self modes column many found state.at.offset
                  { modes | allow = nextIndex (read ++ rest) }
                  (peekIn { modes | allow = nextIndex (read ++ rest) } 0 here.rest))
              read
              rest _
              (Parse.runsFromBindAt middle1 _ _ read [] read rest first _
                (List.appendNil read).flipped
                (line _ middle1 (rewrite offset2, offset1 then arithmetic))
                (middle3 restAt _ _ =>
                  Parse.runsFromBindAt middle3
                    (() => left()) _
                    []
                    []
                    []
                    rest
                    middle3.at.rest _
                    byComputing
                    (runsLeft middle3 rest)
                    (middle4 _ _ _ =>
                      rewrite restAt then
                        match rest with
                          | [next, ..later] =>
                            Parse.runsFromBindAt middle4
                              (() => offset()) _
                              []
                              []
                              []
                              [next, ..later]
                              middle4.at.offset _
                              byComputing
                              (runsOffset middle4 [next, ..later])
                              (middle5 _ _ _ =>
                                let no := andFalseRight (middle4.at.offset != state.at.offset) many _ ends
                                match again: (middle4.at.offset != state.at.offset)
                                  && many
                                  && next.leaf.token.lineStart
                                  && next.leaf.token.column == column
                                  && !endsBlocks next.kind with
                                  | False => Parse.runsPure [first, ..found] [next, ..later] middle5)
                          | [] => Parse.runsPure [first, ..found] [] middle4)))))

--| Where a block's first line is an expression `value` that runs reading `read`, and what follows
--| doesn't continue the block, `block` runs reading `read` and gives `value`. The read-back meets `ends` with `hangs`:
--| every later line of the item starts right of its column, and the leaf after it is on the same line, a closer or
--| comma left of it, or `:=`.
theorem runsBlockOneLine ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (column: Nat) (many: Bool)
    (state: Parse.State Item) (read rest: List Item) (value: Expr)
    (line: ∀ (kind: LineKind) (middle: Parse.State Item) => middle.at.offset = state.at.offset
      → Parse.RunsFrom middle
        (() => statement self (lineModes (blockModes modes column many) column many (nextIndex (read ++ rest)) kind))
        read
        rest
        (ExprStatement value))
    (ends: continuesAt column rest = False):
    Parse.RunsFrom state (() => block self modes column many) read rest value :=
  let lines :=
    Parse.runsFromMark state
      (here => blockLines (here.left + 1) self (blockModes modes column many) column many [])
      read
      rest
      [ExprStatement value]
      (runsBlockLinesOneLine state.at.left self
        (blockModes modes column many)
        column
        many
        []
        state
        read
        rest
        (ExprStatement value)
        line
        ends)
  Parse.runsFromBindAt state _ blockResult read [] read rest
    [ExprStatement value]
    value
    (List.appendNil read).flipped
    lines
    (middle _ _ _ => Parse.runsPure value rest middle)

-- The items of printed leaves: what the parser learns from spans, recomputed from the leaves alone.

--| Where `itemsAfter` is in a list of leaves: the token before, the next item's index, the brackets open and the
--| column of the current line's first token.
type ItemsAt = { before: Option Token, index: Nat, depth: Nat, lineIndent: Nat }

--| The start of a declaration's leaves (`items`).
def ItemsAt.start: ItemsAt := { before = None, index = 0, depth = 0, lineIndent = 0 }

def ItemsAt.items (place: ItemsAt) (leaves: List Leaf): List Item :=
  itemsAfter place.before place.index place.depth place.lineIndent leaves

--| Bracket depth after a token.
def depthPast (depth: Nat) (kind: Tok): Nat :=
  if kind.isOpener then depth + 1
  else if kind.isCloser then depth - 1
  else depth

--| The place after one leaf.
def ItemsAt.step (place: ItemsAt) (leaf: Leaf): ItemsAt := {
  before = Some leaf.token,
  index = place.index + 1,
  depth = depthPast place.depth leaf.token.kind,
  lineIndent = if leaf.token.lineStart then leaf.token.column else place.lineIndent
}

--| The place after some leaves.
def ItemsAt.past (place: ItemsAt): List Leaf → ItemsAt
  | [] => place
  | [leaf, ..rest] => (place.step leaf).past rest

theorem itemsStart ∀ (leaves: List Leaf): items leaves = ItemsAt.start.items leaves := byComputing

theorem itemsLeaves ∀ (place: ItemsAt) (leaves: List Leaf): (place.items leaves).map (item => item.leaf) = leaves :=
  match leaves with
    | [] => byComputing
    | [leaf, ..rest] => Eq.cong (Cons leaf) (itemsLeaves (place.step leaf) rest)

-- The line rule over parts of the leaves.

--| The line rule's state after some leaves, or `None` if one breaks it.
def HangState.after (state: HangState): List Leaf → Option HangState
  | [] => Some state
  | [leaf, ..rest] =>
    match state.step leaf with
      | Some next => next.after rest
      | None => None

def hangsAfter (state: Option HangState) (leaves: List Leaf): Bool := match state with
  | Some known => hangsFrom known leaves
  | None => False

--| The line rule holds of leaves read one after another when it holds of the first, and of the rest from where the
--| first left it: what lets the read-back take `hangs` apart along the tree.
theorem hangsAppend ∀ (state: HangState) (first rest: List Leaf):
    hangsFrom state (first ++ rest) = hangsAfter (state.after first) rest :=
  match first with
    | [] => byComputing
    | [leaf, ..more] =>
      match stepped: state.step leaf with
        | Some next => hangsAppend next more rest
        | None => byComputing

--| Whether a leaf would take a block at `column` round again: `continuesAt` of its item.
def continuesLeaf (column: Nat) (leaf: Leaf): Bool :=
  leaf.token.lineStart && leaf.token.column == column && !endsBlocks leaf.token.kind

theorem continuesItem ∀ (column: Nat) (item: Item) (later: List Item):
    continuesAt column [item, ..later] = continuesLeaf column item.leaf :=
  byComputing

--| Inside a bracket whose current item started a line at `column`, a leaf the line rule accepts doesn't take that
--| item's block round again: `runsBlockOneLine`'s `ends`, from `hangs`.
theorem stepInBracket ∀ (state next: HangState) (leaf: Leaf) (column: Nat) (outer: List (Option Nat))
    (inside: state.blocks = [Some column, ..outer])
    (stepped: state.step leaf = Some next):
    continuesLeaf column leaf = False :=
  match state with | { blocks, top, start, glue } => rewrite inside at stepped then cases

--| Likewise for the type or the body, which started a line at `column`, outside brackets.
theorem stepAtTop ∀ (state next: HangState) (leaf: Leaf) (column: Nat)
    (outside: state.blocks = [])
    (top: state.top = Some column)
    (stepped: state.step leaf = Some next):
    continuesLeaf column leaf = False :=
  match state with | { blocks, top = above, start, glue } => rewrite outside, top at stepped then cases

--| A closer at column 2 on its own line, its item at 4: `stepInBracket`'s hypotheses can hold.
theorem stepInBracketExample: continuesLeaf 4 {
      token = { kind = RParen, text = ")", column = 2, lineStart = True },
      trivia = Trivia.empty
    }
      = False :=
  stepInBracket
    { blocks = [Some 4], top = None, start = False, glue = False }
    { blocks = [], top = None, start = False, glue = False }
    { token = { kind = RParen, text = ")", column = 2, lineStart = True }, trivia = Trivia.empty }
    4
    []
    byComputing
    byComputing

--| `:=` at the type's column 2: `stepAtTop`'s hypotheses can hold.
theorem stepAtTopExample: continuesLeaf 2 {
      token = { kind = ColonEq, text = ":=", column = 2, lineStart = True },
      trivia = Trivia.empty
    }
      = False :=
  stepAtTop
    { blocks = [], top = Some 2, start = False, glue = False }
    { blocks = [], top = None, start = True, glue = False }
    { token = { kind = ColonEq, text = ":=", column = 2, lineStart = True }, trivia = Trivia.empty }
    2
    byComputing
    byComputing
    byComputing
