--| Slice 1's read-back (docs/proposals/self-hosted-fmt-s1-sketch.md §2, ticket 17): leaves that spell a tree and
--| `hangs` parse back to it. This file starts with the block lemma the rest stands on: where the next line doesn't
--| start at a block's column, `block` reads one line and `blockLines` doesn't go round.

namespace Syntax.ReadBackProofs
import Std (Bool, DecEq, Eq, List, Nat, Option, Parse, Text)
import Syntax (..)
import Fmt (..)

-- Reading from one mark.

--| A parser that looks at where it is, `k (Parse.mark())`, read from `start` as `k start` is.
theorem readsAtMark ∀ (k: Parse.Mark t → {Parse t} a) (spec: List t → a → Prop) (start: Parse.Mark t)
    (each: Parse.ReadsAt start (() => k start) spec):
    Parse.ReadsAt start (() => k (Parse.mark())) spec :=
  total state value after here honest h =>
    let ran: Parse.runFrom state (() => (k state.at, Parse.mark())) = Ok (value, after) := h
    each total state value after here honest (rewrite <- here then ran)

--| `offset` reads nothing and gives the mark's offset.
theorem readsAtOffset ∀ (start: Parse.Mark Item):
    Parse.ReadsAt start (() => offset()) (read at => read = [] ∧ at = start.offset) :=
  readsAtMark (here => here.offset) _ start (Parse.readsAtDone start start.offset _ (byComputing, byComputing))

--| `left` reads nothing and gives the items left.
theorem readsAtLeft ∀ (start: Parse.Mark Item):
    Parse.ReadsAt start (() => left()) (read items => read = [] ∧ items = start.rest) :=
  readsAtMark (here => here.rest) _ start (Parse.readsAtDone start start.rest _ (byComputing, byComputing))

--| `peek` reads nothing.
theorem readsAtPeekNothing ∀ (modes: Modes) (start: Parse.Mark Item):
    Parse.ReadsAt start (() => modes.peek) (read found => read = [] ∧ found = peekIn modes 0 start.rest) :=
  readsAtMark (here => peekIn modes 0 here.rest) _ start (Parse.readsAtDone start _ _ (byComputing, byComputing))

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

--| `blockLines` reads one line where its statement reads as `line` says and what follows doesn't continue the block.
--|
--| Proof idea: the offset, `left`, the peek and `left` again read nothing, so the statement starts where the round did; after it,
--| `ends` makes the test for another round false.
theorem blockLinesOneLine ∀ (more: Nat) (self: Goal → {Parse Item} Expr) (modes: Modes) (column: Nat) (many: Bool)
    (found: List Statement) (start: Parse.Mark Item) (line: List Item → Statement → Prop)
    (reads: ∀ (at: Parse.Mark Item) (kind: LineKind) => at.rest = start.rest
      → Parse.ReadsAt at (() => statement self (lineModes modes column many (nextIndex start.rest) kind)) line)
    (ends: ∀ (read later: List Item) (first: Statement) => start.rest = read ++ later
      → line read first
      → continuesAt column later = False):
    Parse.ReadsAt start (() => blockLines (Succ more) self modes column many found) (read lines =>
      ∃ (first: Statement) => lines = [first, ..found] ∧ line read first) :=
  Parse.readsAtThen (readsAtOffset start) (read before after starts (none, same) =>
    Parse.readsAtThen (readsAtLeft after) (read1 items after1 starts1 (none1, sameItems) =>
      Parse.readsAtThen (readsAtPeekNothing _ after1) (read2 seen after2 starts2 (none2, _) =>
        let at2: after2.rest = start.rest := calc after2.rest
          _ = read ++ read1 ++ read2 ++ after2.rest := rewrite none, none1, none2
          _ = start.rest := rewrite starts, starts1, starts2
        let itemsAre: items = start.rest := calc items
          _ = after.rest := sameItems
          _ = read ++ after.rest := rewrite none
          _ = start.rest := starts.flipped
        rewrite same, itemsAre then
          Parse.readsAtThen (reads after2 (lineKindOf seen) at2) (read3 statement1 after3 starts3 holds =>
            let noMore: continuesAt column after3.rest = False :=
              ends read3 after3.rest statement1 (rewrite <- at2 then starts3) holds
            Parse.readsAtThen (readsAtLeft after3) (read4 items after4 starts4 (none4, sameItems) =>
              match items with
                | [next, ..later] => Parse.readsAtThen (readsAtOffset after4) (read5 now after5 starts5 (none5, _) =>
                  let stops: continuesAt column [next, ..later] = False := rewrite sameItems then noMore
                  rewrite andFalseRight (now != start.offset) many _ stops then
                    Parse.readsAtDone after5 _ _ (
                      statement1,
                      byComputing,
                      rewrite none, none1, none2, none4, none5, List.appendNil read3 then holds
                    ))
                | [] => Parse.readsAtDone after4 _ _ (
                  statement1,
                  byComputing,
                  rewrite none, none1, none2, none4, List.appendNil read3 then holds
                ))))))

--| The modes `block` reads its lines with.
def blockModes (modes: Modes) (column: Nat) (many: Bool): Modes :=
  if many then { modes | limit = Some column, letValue = None } else { modes | limit = Some column }

--| `blockOneLine` (sketch §2, ticket 17): where what follows a block's first line doesn't start a line at the block's
--| column (or ends blocks), `block` reads that one line, and what it gives is the line's expression.
theorem blockOneLine ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (column: Nat) (many: Bool)
    (start: Parse.Mark Item) (line: List Item → Statement → Prop)
    (reads: ∀ (at: Parse.Mark Item) (kind: LineKind) => at.rest = start.rest
      → Parse.ReadsAt at
        (() => statement self (lineModes (blockModes modes column many) column many (nextIndex start.rest) kind))
        line)
    (ends: ∀ (read later: List Item) (first: Statement) => start.rest = read ++ later
      → line read first
      → continuesAt column later = False):
    Parse.ReadsAt start (() => block self modes column many) (read value => line read (ExprStatement value)) :=
  let lines :=
    readsAtMark
      (here => blockLines (here.left + 1) self (blockModes modes column many) column many []) _
      start
      (blockLinesOneLine start.left self (blockModes modes column many) column many [] start line reads ends)
  Parse.readsAtThen [j := blockResult] lines (read found after starts (first, (same, holds)) =>
    rewrite same then
      match first with
        | ExprStatement value => Parse.readsAtDone after value _ (rewrite List.appendNil read then holds)
        | LetStatement _ => Parse.readsFatal [inv := Parse.Invariant.any] _ _ after { holds = Trivial }
        | LocalDef _ _ _ => Parse.readsFatal [inv := Parse.Invariant.any] _ _ after { holds = Trivial })

-- Blocks, run: the completeness half, what the read-back builds on.

theorem runsOffset ∀ (state: Parse.State Item) (rest: List Item):
    Parse.RunsFrom state (() => offset()) [] rest state.at.offset :=
  Parse.runsFromMark state (here => here.offset) [] rest state.at.offset (Parse.runsPure state.at.offset rest state)

theorem runsLeft ∀ (state: Parse.State Item) (rest: List Item):
    Parse.RunsFrom state (() => left()) [] rest state.at.rest :=
  Parse.runsFromMark state (here => here.rest) [] rest state.at.rest (Parse.runsPure state.at.rest rest state)

theorem runsPeek ∀ (modes: Modes) (state: Parse.State Item) (rest: List Item):
    Parse.RunsFrom state (() => modes.peek) [] rest (peekIn modes 0 state.at.rest) :=
  Parse.runsFromMark state (here => peekIn modes 0 here.rest) [] rest _ (Parse.runsPure _ rest state)

--| `blockLines` runs one round: from `state`, where the line's statement runs reading `read`, and what follows it
--| doesn't continue the block.
--|
--| Proof idea: as `blockLinesOneLine`, from the other side: each step that reads nothing runs from any state, the
--| statement from where the round started, and `ends` makes the test for another round false.
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

--| `blockOneLine`, run: where a block's first line is an expression `value` that runs reading `read`, and what follows
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

--| The first item: its leaf, with what it is glued to and its place.
theorem itemsCons ∀ (place: ItemsAt) (leaf: Leaf) (rest: List Leaf):
    place.items [leaf, ..rest]
      = [
        {
          leaf,
          glued = match place.before with
            | Some previous => !leaf.token.lineStart && endColumn previous == leaf.token.column
            | None => False,
          afterOperand = place.before.map (previous => previous.kind.closesOperand) |> .getOrElse False,
          afterDot = place.before.map (previous => previous.kind == Dot) |> .getOrElse False,
          index = place.index,
          depth = place.depth,
          lineIndent = if leaf.token.lineStart then leaf.token.column else place.lineIndent
        },
        ..(place.step leaf).items rest
      ] :=
  byComputing

--| The items of leaves read one after another are the first leaves' items, then the rest's from where they end.
theorem itemsAppend ∀ (place: ItemsAt) (first rest: List Leaf):
    place.items (first ++ rest) = place.items first ++ (place.past first).items rest :=
  match first with
    | [] => byComputing
    | [leaf, ..more] =>
      let inner := itemsAppend (place.step leaf) more rest
      rewrite inner

theorem itemsLeaves ∀ (place: ItemsAt) (leaves: List Leaf): (place.items leaves).map (item => item.leaf) = leaves :=
  match leaves with
    | [] => byComputing
    | [leaf, ..rest] => Eq.cong (Cons leaf) (itemsLeaves (place.step leaf) rest)

theorem itemsLength ∀ (place: ItemsAt) (leaves: List Leaf): (place.items leaves).length = leaves.length :=
  match leaves with
    | [] => byComputing
    | [leaf, ..rest] => Eq.cong Succ (itemsLength (place.step leaf) rest)

--| Each leaf moves the index on by one, so the items of a declaration are numbered by their offsets.
theorem pastIndex ∀ (place: ItemsAt) (leaves: List Leaf): (place.past leaves).index = place.index + leaves.length :=
  match leaves with
    | [] => arithmetic
    | [leaf, ..rest] => arithmetic [pastIndex (place.step leaf) rest]

theorem pastAppend ∀ (place: ItemsAt) (first rest: List Leaf):
    place.past (first ++ rest) = (place.past first).past rest :=
  match first with
    | [] => byComputing
    | [leaf, ..more] => pastAppend (place.step leaf) more rest

--| After a leaf, the token before is that leaf's: what `glued`, `afterOperand` and `afterDot` of the next item read.
theorem pastLast ∀ (place: ItemsAt) (first: List Leaf) (leaf: Leaf):
    (place.past (first ++ [leaf])).before = Some leaf.token :=
  rewrite pastAppend place first [leaf]

--| Whether leaves close every bracket they open, `open` brackets being open already: no closer below the start.
def balancedFrom (open: Nat): List Leaf → Bool
  | [] => open == 0
  | [leaf, ..rest] =>
    if leaf.token.kind.isOpener then balancedFrom (open + 1) rest
    else if leaf.token.kind.isCloser then open > 0 && balancedFrom (open - 1) rest
    else balancedFrom open rest

def ItemsAt.balanced (leaves: List Leaf): Bool := balancedFrom 0 leaves

--| The brackets left open after a token, of those the leaves opened.
def openPast (open: Nat) (kind: Tok): Nat :=
  if kind.isOpener then open + 1
  else if kind.isCloser then open - 1
  else open

--| One leaf of balanced leaves: the rest are balanced from the brackets now open, the depth still counts them, and
--| the depth before is found from the depth after.
theorem balancedStep ∀ (depth open: Nat) (leaf: Leaf) (rest: List Leaf)
    (inside: open <= depth) (balanced: balancedFrom open [leaf, ..rest]):
    balancedFrom (openPast open leaf.token.kind) rest
      ∧ openPast open leaf.token.kind <= depthPast depth leaf.token.kind
      ∧ (∀ (x: Nat) => x + openPast open leaf.token.kind = depthPast depth leaf.token.kind → x + open = depth) :=
  match opener: leaf.token.kind.isOpener with
    | True => (balanced, arithmetic, x same => arithmetic [same])
    | False =>
      match closer: leaf.token.kind.isCloser with
        | True =>
          let some: open > 0 := Bool.andLeft balanced
          (Bool.andRight balanced, arithmetic [inside, some], x same => arithmetic [same, inside, some])
        | False => (balanced, inside, x same => same)

--| Leaves with brackets balanced leave the depth as it was: a subtree's items are at the depth of its first.
--|
--| Proof idea: by induction on the leaves, with `open` the brackets the leaves so far left open, which the depth
--| counts; `balancedStep` takes one leaf.
theorem pastDepthOpen ∀ (place: ItemsAt) (open: Nat) (leaves: List Leaf)
    (inside: open <= place.depth) (balanced: balancedFrom open leaves):
    (place.past leaves).depth + open = place.depth :=
  match leaves with
    | [] =>
      let none: open = 0 := DecEq.sound balanced
      arithmetic [none]
    | [leaf, ..rest] =>
      let (more, deeper, back) := balancedStep place.depth open leaf rest inside balanced
      back _ (pastDepthOpen (place.step leaf) (openPast open leaf.token.kind) rest deeper more)

theorem pastDepth ∀ (place: ItemsAt) (leaves: List Leaf) (balanced: balancedFrom 0 leaves):
    (place.past leaves).depth = place.depth :=
  let same := pastDepthOpen place 0 leaves (arithmetic) balanced
  arithmetic [same]

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
--| item's block round again: `blockOneLine`'s `ends`, from `hangs`.
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
