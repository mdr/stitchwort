--| Slice 1's read-back (docs/proposals/self-hosted-fmt-s1-sketch.md §2, ticket 17): leaves that spell a tree and
--| `hangs` parse back to it. This file starts with the block lemma the rest stands on: where the next line doesn't
--| start at a block's column, `block` reads one line and `blockLines` doesn't go round.

namespace Syntax.ReadBackProofs
import Std (Bool, Eq, List, Nat, Option, Parse, Text)
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

--| The modes `blockLines` reads a line with, from offset `before`, the line being of `kind`.
def lineModes (modes: Modes) (column: Nat) (many: Bool) (before: Nat) (kind: LineKind): Modes :=
  { { modes | allow = Some before } | lines = [{ column, many, kind }, ..modes.lines] }

--| `lineKind` reads nothing.
theorem readsAtLineKind ∀ (modes: Modes) (start: Parse.Mark Item):
    Parse.ReadsAt start (() => lineKind modes) (read kind => read = []) :=
  Parse.readsAtThen (readsAtPeekNothing modes start) (read found after starts (none, _) =>
    Parse.readsAtDone after (lineKindOf found) _ (rewrite none))

theorem andFalseRight ∀ (a b c: Bool) (no: c = False): (a && b && c) = False := match a, b with
  | True, True => no
  | True, False => byComputing
  | False, _ => byComputing

--| `blockAgain` reads nothing, and says no where the next item doesn't continue the block.
theorem readsAtBlockAgain ∀ (before column: Nat) (many: Bool) (start: Parse.Mark Item):
    Parse.ReadsAt start (() => blockAgain before column many) (read again =>
      read = [] ∧ (continuesAt column start.rest = False → again = False)) :=
  Parse.readsAtThen (readsAtOffset start) (read at after starts (none, _) =>
    Parse.readsAtThen (readsAtLeft after) (read2 items after2 starts2 (none2, same) =>
      match items with
        | [next, ..later] => Parse.readsAtDone after2 _ _ (
          rewrite none, none2 then byComputing,
          stops =>
            let restSame: start.rest = [next, ..later] := calc start.rest
              _ = read ++ after.rest := starts
              _ = [next, ..later] := rewrite none, <- same
            andFalseRight (at != before) many _ (rewrite restSame at stops then stops)
        )
        | [] => Parse.readsAtDone after2 False _ (rewrite none, none2 then byComputing, stops => byComputing)))

theorem blockLinesOneLine ∀ (more: Nat) (self: Goal → {Parse Item} Expr) (modes: Modes) (column: Nat) (many: Bool)
    (found: List Statement) (start: Parse.Mark Item) (line: List Item → Statement → Prop)
    (reads: ∀ (at: Parse.Mark Item) (kind: LineKind) => at.rest = start.rest
      → Parse.ReadsAt at (() => statement self (lineModes modes column many start.offset kind)) line)
    (ends: ∀ (read later: List Item) (read1: Statement) => start.rest = read ++ later
      → line read read1
      → continuesAt column later = False):
    Parse.ReadsAt start (() => blockLines (Succ more) self modes column many found) (read lines =>
      ∃ (first: Statement) => lines = [first, ..found] ∧ line read first) :=
  Parse.readsAtThen (readsAtOffset start) (read before after starts (none, same) =>
    Parse.readsAtThen (readsAtLineKind _ after) (read2 kind after2 starts2 none2 =>
      let at2: after2.rest = start.rest := calc after2.rest
        _ = read ++ read2 ++ after2.rest := rewrite none, none2
        _ = start.rest := rewrite starts, starts2
      rewrite same then
        Parse.readsAtThen (reads after2 kind at2) (read3 statement1 after3 starts3 holds =>
          let noMore: continuesAt column after3.rest = False :=
            ends read3 after3.rest statement1 (rewrite <- at2 then starts3) holds
          Parse.readsAtThen (readsAtBlockAgain start.offset column many after3) (read4 again after4 starts4 (none4,
            says) =>
            rewrite says noMore then
              Parse.readsAtDone after4 _ _ (
                statement1,
                byComputing,
                rewrite none, none2, none4, List.appendNil read3 then holds
              )))))

--| The modes `block` reads its lines with.
def blockModes (modes: Modes) (column: Nat) (many: Bool): Modes :=
  if many then { modes | limit = Some column, letValue = None } else { modes | limit = Some column }

--| `blockOneLine` (sketch §2, ticket 17): where what follows a block's first line doesn't start a line at the block's
--| column (or ends blocks), `block` reads that one line, and what it gives is the line's expression. The read-back
--| meets `ends` with `hangs`: every later line of the item starts right of its column, and the leaf after it is a
--| closer or comma left of it, or on the same line.
theorem blockOneLine ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (column: Nat) (many: Bool)
    (start: Parse.Mark Item) (line: List Item → Statement → Prop)
    (reads: ∀ (at: Parse.Mark Item) (kind: LineKind) => at.rest = start.rest
      → Parse.ReadsAt at
        (() => statement self (lineModes (blockModes modes column many) column many start.offset kind))
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
  Parse.readsAtThen lines (read found after starts (first, (same, holds)) =>
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

theorem runsLineKind ∀ (modes: Modes) (state: Parse.State Item) (rest: List Item):
    Parse.RunsFrom state (() => lineKind modes) [] rest (lineKindOf (peekIn modes 0 state.at.rest)) :=
  Parse.runsFromBindAt state
    (() => modes.peek)
    (found => lineKindOf found)
    []
    []
    []
    rest _ _
    byComputing
    (runsPeek modes state rest)
    (middle _ _ _ => Parse.runsPure _ rest middle)

theorem runsBlockAgain ∀ (before column: Nat) (many: Bool) (state: Parse.State Item) (rest: List Item)
    (ends: continuesAt column rest = False):
    Parse.RunsFrom state (() => blockAgain before column many) [] rest False :=
  Parse.runsFromBindAt state
    (() => offset()) _
    []
    []
    []
    rest
    state.at.offset
    False
    byComputing
    (runsOffset state rest)
    (middle restAt _ _ =>
      Parse.runsFromBindAt middle
        (() => left()) _
        []
        []
        []
        rest
        middle.at.rest
        False
        byComputing
        (runsLeft middle rest)
        (inner _ _ _ =>
          rewrite restAt then
            match rest with
              | [next, ..later] =>
                rewrite andFalseRight (state.at.offset != before) many _ ends then
                  Parse.runsPure False [next, ..later] inner
              | [] => Parse.runsPure False [] inner))

--| `blockLines` runs one round: from `state`, where the line's statement runs reading `read`, and what follows it
--| doesn't continue the block.
theorem runsBlockLinesOneLine ∀ (more: Nat) (self: Goal → {Parse Item} Expr) (modes: Modes) (column: Nat) (many: Bool)
    (found: List Statement) (state: Parse.State Item) (read rest: List Item) (first: Statement)
    (line: ∀ (kind: LineKind) (middle: Parse.State Item) => middle.at.offset = state.at.offset
      → Parse.RunsFrom middle (() => statement self (lineModes modes column many state.at.offset kind)) read rest first)
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
    (middle _ _ offset1 =>
      Parse.runsFromBindAt middle
        (() => lineKind { modes | allow = Some state.at.offset }) _
        []
        read
        read
        rest _ _
        byComputing
        (runsLineKind _ middle (read ++ rest))
        (middle2 _ _ offset2 =>
          Parse.runsFromBindAt middle2 _ _ read [] read rest first _
            (List.appendNil read).flipped
            (line _ middle2 (rewrite offset2, offset1 then arithmetic))
            (middle3 _ _ _ =>
              Parse.runsFromBindAt middle3
                (() => blockAgain state.at.offset column many) _
                []
                []
                []
                rest
                False _
                byComputing
                (runsBlockAgain state.at.offset column many middle3 rest ends)
                (middle4 _ _ _ => Parse.runsPure [first, ..found] rest middle4))))

--| `blockOneLine`, run: where a block's first line is an expression `value` that runs reading `read`, and what follows
--| doesn't continue the block, `block` runs reading `read` and gives `value`. The read-back meets `ends` with `hangs`:
--| every later line of the item starts right of its column, and the leaf after it is on the same line, a closer or
--| comma left of it, or `:=`.
theorem runsBlockOneLine ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (column: Nat) (many: Bool)
    (state: Parse.State Item) (read rest: List Item) (value: Expr)
    (line: ∀ (kind: LineKind) (middle: Parse.State Item) => middle.at.offset = state.at.offset
      → Parse.RunsFrom middle
        (() => statement self (lineModes (blockModes modes column many) column many state.at.offset kind))
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
  Parse.runsFromBindAt state _ _ read [] read rest
    [ExprStatement value]
    value
    (List.appendNil read).flipped
    lines
    (middle _ _ _ => Parse.runsPure value rest middle)
