--| Rule N, where each comment belongs (docs/proposals/fmt-passes.md §2):
--| `crates/fmt`'s `place_comments` (`tidy.rs`), as functions on the
--| lexer's leaves, to run every time tokens are read. After it:
--|
--| 1. no comma, closing bracket or record update's `|` has a trailing
--|    comment, except one kept because moving it would pass comments;
--| 2. no comma has any comment;
--| 3. no `->` has a trailing comment, nor own-line comments after it: they
--|    come before the `->`;
--| 4. an expression `let`'s `:=` has no trailing comment: it comes before;
--| 5. no comment's text ends in a space.
--|
--| Each step is a pass over the leaves, in the Rust order. A pass that
--| looks back keeps the leaves before the current one newest first, as the
--| toy's `homeStep` does, so a step back is a step down a list.

namespace Syntax
import Std (Bool, List, Nat, Option, Text)

def Leaf.kind (leaf: Leaf): Tok := leaf.token.kind

def Leaf.withTrailing (leaf: Leaf) (trailing: Option Comment): Leaf := { leaf | trivia = { leaf.trivia | trailing } }

def Leaf.withLeading (leaf: Leaf) (leading: List Comment): Leaf := { leaf | trivia = { leaf.trivia | leading } }

def Comment.unspaced (comment: Comment): Comment := { comment | blankLines = 0 }

-- Rule 1: a comment after closers, commas and a record update's `|` goes
-- back to the code before them.

--| Whether `bar`, a `|` between `behind` (newest first) and `ahead`, is a record
--| update's, `{ r | … }`: the first `|` at its depth after an opening brace
--| that opens a record, with no comma before it.
def recordBar (bar: Leaf) (behind ahead: List Leaf): Bool :=
  openingBrace behind 0 []
    |> .map (between => !separated between 0 && recordBraces (between ++ [bar, ..ahead]))
    |> .getOrElse False

--| The leaves after the nearest unclosed `{` in `behind` (newest first), in
--| order, if there is one. An unclosed `(` or `[` is passed over.
def openingBrace (behind: List Leaf) (depth: Nat) (between: List Leaf): Option (List Leaf) := match behind with
  | [] => None
  | [leaf, ..earlier] =>
    match leaf.kind with
      | LBrace => if depth == 0 then Some between else openingBrace earlier (depth - 1) [leaf, ..between]
      | LParen => openingBrace earlier (depth - 1) [leaf, ..between]
      | LBracket => openingBrace earlier (depth - 1) [leaf, ..between]
      | kind => openingBrace earlier (if kind.isCloser then depth + 1 else depth) [leaf, ..between]

--| Whether a comma, `|` or `=>` stands at the outer depth of `leaves`.
def separated (leaves: List Leaf) (depth: Nat): Bool := match leaves with
  | [] => False
  | [leaf, ..rest] =>
    match leaf.kind with
      | Comma => depth == 0 || separated rest depth
      | Pipe => depth == 0 || separated rest depth
      | FatArrow => depth == 0 || separated rest depth
      | kind =>
        if kind.isOpener then separated rest (depth + 1)
        else if kind.isCloser then separated rest (depth - 1)
        else separated rest depth

--| Whether braces whose contents start `inside` hold a record
--| (`crates/syntax`'s `record_braces`): not a binder `{x: T}`, and either a
--| field `=` at their depth, or a lowercase start and no atom after them.
def recordBraces (inside: List Leaf): Bool := match inside with
  | [first, second, .._] if first.kind == Lower && second.kind == Colon => False
  | _ =>
    let first := inside.head.map Leaf.kind
    match fieldOrClose inside 0 with
      | FieldFound => True
      | Unclosed => False
      | ClosedBefore after =>
        if first == Some Upper then False
        else
          after.head.map (leaf => !(leaf.kind.opensAtom || leaf.kind == TypeU || leaf.kind == PropU))
            |> .getOrElse False

type BraceScan =
  | FieldFound
  | Unclosed
  --| The closing brace, with the leaves after it.
  | ClosedBefore (after: List Leaf)

def fieldOrClose (leaves: List Leaf) (depth: Nat): BraceScan := match leaves with
  | [] => Unclosed
  | [leaf, ..rest] =>
    match leaf.kind with
      | Equals if depth == 0 => FieldFound
      | RBrace if depth == 0 => ClosedBefore rest
      | kind =>
        if kind.isOpener then fieldOrClose rest (depth + 1)
        else if kind.isCloser && depth > 0 then fieldOrClose rest (depth - 1)
        else fieldOrClose rest depth

--| Whether rule 1 walks past a leaf: a comma, a closer, or a record
--| update's `|`.
def skipped (leaf: Leaf) (behind ahead: List Leaf): Bool := match leaf.kind with
  | Comma => True
  | Pipe => recordBar leaf behind ahead
  | kind => kind.isCloser

--| Whether a trailing comment on the leaf may move: on a comma that doesn't
--| start its line, a closer, or a record update's `|`.
def movable (leaf: Leaf) (behind ahead: List Leaf): Bool := match leaf.kind with
  | Comma => !leaf.token.lineStart
  | Pipe => recordBar leaf behind ahead
  | kind => kind.isCloser

--| Whether the line ending at the head of `line` (newest first) ends with a
--| comment: on that leaf, or on the leaf rule 1 has moved it back to, past
--| the closers, commas and bars before it (SW-3606).
def endsWithComment (line ahead: List Leaf): Bool := match line with
  | [] => False
  | [leaf, ..earlier] =>
    if leaf.trivia.trailing.isSome then True
    else if earlier.isEmpty || !skipped leaf earlier ahead then False
    else endsWithComment earlier [leaf, ..ahead]

--| Whether rule 1's walk takes `current`, with `behind` (newest first) the
--| leaves before it, to start its line. With `bareLast`, the last commas
--| are bare ones standing for commas the P2 pass deletes from the text
--| (`settledOnce`), so a closer right after a last comma that starts its
--| line counts as starting it, as it would with the comma deleted.
def startsWalk (bareLast: Bool) (current: Leaf) (behind: List Leaf): Bool := match bareLast with
  | False => current.token.lineStart
  | True =>
    match behind with
      | [previous, ..earlier] =>
        current.token.lineStart
          || current.kind.isCloser && previous.kind == Comma && previous.token.lineStart && hasItem earlier
      | [] => current.token.lineStart

--| How many leaves back a trailing comment on `current` moves: past
--| commas, closers and bars, stopping on one that starts its line
--| (`startsWalk`) if going further would pass its own-line comments or a
--| comment ending the line before.
def stepsBack (bareLast: Bool) (current: Leaf) (behind ahead: List Leaf) (steps: Nat): Nat := match behind with
  | [] => steps
  | [previous, ..earlier] =>
    if !skipped current behind ahead then steps
    else if startsWalk bareLast current behind
      && (!current.trivia.leading.isEmpty || endsWithComment behind [current, ..ahead]) then
      steps
    else stepsBack bareLast previous earlier [current, ..ahead] (steps + 1)

--| `behind` (newest first) with the comment on the leaf `steps` back
--| from its head, counting the head as 1.
def trailingAt (behind: List Leaf) (steps: Nat) (comment: Comment): List Leaf := match behind, steps with
  | [leaf, ..earlier], Succ Zero => [leaf.withTrailing (Some comment), ..earlier]
  | [leaf, ..earlier], Succ more => [leaf, ..trailingAt earlier more comment]
  | _, _ => behind

--| Whether a bar's trailing comment that stays starts the line below
--| instead: the base's comment is printed after the bar, so the bar's own
--| would run into it on one line.
def barBelow (leaf: Leaf) (behind ahead: List Leaf): Bool := match leaf.kind, behind, ahead with
  | Pipe, [previous, .._], [_, .._] => previous.trivia.trailing.isSome
  | _, _, _ => False

--| Rule 1 over `rest`, with `behind` the leaves already settled, newest
--| first, and `bumped` a comment for the next leaf's own-line comments;
--| `bareLast` as for `startsWalk`.
def homeFrom (bareLast: Bool) (behind: List Leaf) (bumped: Option Comment) (rest: List Leaf): List Leaf :=
  match rest with
    | [] => behind.reverse
    | [leaf, ..after] =>
      let leaf := bumped.map (comment => leaf.withLeading [comment, ..leaf.trivia.leading]) |> .getOrElse leaf
      match leaf.trivia.trailing with
        | Some comment if movable leaf behind after =>
          match stepsBack bareLast leaf behind after 0 with
            | Zero =>
              if barBelow leaf behind after then
                homeFrom bareLast [leaf.withTrailing None, ..behind] (Some comment.unspaced) after
              else homeFrom bareLast [leaf, ..behind] None after
            | steps => homeFrom bareLast [leaf.withTrailing None, ..trailingAt behind steps comment] None after
        | _ => homeFrom bareLast [leaf, ..behind] None after

-- Rule 2: a comma's comments go to the token after it.

--| Own-line comments carried from a comma to the next leaf, and the blank
--| lines before them.
type Carried = { comments: List Comment, blankLines: Nat }

--| `trivia` with the carried comments in front of its own, the blank lines
--| counted once.
def Carried.into (carried: Carried) (trivia: Trivia): Trivia := match trivia.leading with
  | [first, ..more] => { trivia |
    leading = carried.comments ++ [{ first | blankLines = Nat.max first.blankLines carried.blankLines }, ..more]
  }
  | [] => { trivia | leading = carried.comments, blankLines = Nat.max trivia.blankLines carried.blankLines }

--| What a comma holds, to carry on, if anything: its own-line comments, then
--| its trailing comment with the comma's blank lines.
def commaCarries (trivia: Trivia): Option Carried := match trivia.leading, trivia.trailing with
  | [], None => None
  | leading, Some comment =>
    Some { comments = leading ++ [{ comment | blankLines = trivia.blankLines }], blankLines = 0 }
  | leading, None => Some { comments = leading, blankLines = trivia.blankLines }

--| Rule 2 over `rest`, `done` newest first, then the end of the file's
--| trivia with anything still carried.
def commasFrom (done: List Leaf) (carried: Option Carried) (rest: List Leaf) (end: Trivia): Lexed :=
  let receive := (trivia: Trivia) => carried.map (carry => carry.into trivia) |> .getOrElse trivia
  match rest with
    | [] => { leaves = done.reverse, end = receive end }
    | [leaf, ..after] =>
      let leaf := { leaf | trivia = receive leaf.trivia }
      match commaCarries leaf.trivia with
        | Some carry if leaf.kind == Comma =>
          commasFrom [{ leaf | trivia = Trivia.empty }, ..done] (Some carry) after end
        | _ => commasFrom [leaf, ..done] None after end

-- Rule 3: comments after `->` go before it.

def arrowsFrom (done: List Leaf) (current: Leaf) (rest: List Leaf): List Leaf := match rest with
  | [] => [current, ..done].reverse
  | [next, ..more] =>
    if current.kind == Arrow && (!next.trivia.leading.isEmpty || current.trivia.trailing.isSome) then
      let own := current.trivia.trailing.map (comment => [comment.unspaced]) |> .getOrElse []
      let current := { current |
        trivia = { current.trivia | leading = current.trivia.leading ++ own ++ next.trivia.leading, trailing = None }
      }
      arrowsFrom [current, ..done] (next.withLeading []) more
    else arrowsFrom [current, ..done] next more

def arrows (leaves: List Leaf): List Leaf := match leaves with
  | [] => []
  | [first, ..rest] => arrowsFrom [] first rest

-- Rule 4: an expression `let`'s value must start on its `:=` line (SW-3750),
-- so a comment ending that line goes before the `:=`.

--| Whether a `let` at the outer depth comes before the `:=`, in `behind`
--| (newest first), within its expression.
def letBefore (behind: List Leaf) (depth: Nat): Bool := match behind with
  | [] => False
  | [leaf, ..earlier] =>
    let kind := leaf.kind
    if kind.isCloser then letBefore earlier (depth + 1)
    else if kind.isOpener then depth > 0 && letBefore earlier (depth - 1)
    else if depth > 0 then letBefore earlier depth
    else if kind == KwLet then True
    else if kind == Semi || kind == FatArrow || kind.startsDeclaration then False
    else letBefore earlier depth

--| Whether a `;` at the outer depth comes after the `:=`, before its
--| expression closes.
def semicolonAfter (ahead: List Leaf) (depth: Nat): Bool := match ahead with
  | [] => False
  | [leaf, ..later] =>
    let kind := leaf.kind
    if kind.isOpener then semicolonAfter later (depth + 1)
    else if kind.isCloser then depth > 0 && semicolonAfter later (depth - 1)
    else if kind == Semi && depth == 0 then True
    else semicolonAfter later depth

def letsFrom (behind rest: List Leaf): List Leaf := match rest with
  | [] => behind.reverse
  | [leaf, ..after] =>
    match leaf.trivia.trailing with
      | Some comment if leaf.kind == ColonEq && letBefore behind 0 && semicolonAfter after 0 =>
        let moved :=
          { leaf | trivia = { leaf.trivia | leading = leaf.trivia.leading ++ [comment.unspaced], trailing = None } }
        letsFrom [moved, ..behind] after
      | _ => letsFrom [leaf, ..behind] after

-- Rule 5: comment text loses its trailing spaces.

def Comment.trimmed (comment: Comment): Comment := { comment | text = trimEnd comment.text }

--| The text without the spaces at its end.
def trimEnd (text: Text): Text :=
  if text.endsWith " " then Text.fromList (text.toList.reverse.dropWhile (char => char == ' ')).reverse else text

def Trivia.trimmed (trivia: Trivia): Trivia :=
  { trivia | leading = trivia.leading.map Comment.trimmed, trailing = trivia.trailing.map Comment.trimmed }

--| The leaves with each comment where rule N puts it, `bareLast` as for
--| `startsWalk`.
def Lexed.settledWith (lexed: Lexed) (bareLast: Bool): Lexed :=
  let homed := homeFrom bareLast [] None lexed.leaves
  let commas := commasFrom [] None homed lexed.end
  let leaves := letsFrom [] (arrows commas.leaves)
  { leaves = leaves.map (leaf => { leaf | trivia = leaf.trivia.trimmed }), end = commas.end.trimmed }

--| The lexer's leaves with each comment where rule N puts it, as
--| `crates/fmt`'s `place_comments` does.
def Lexed.settled (lexed: Lexed): Lexed := lexed.settledWith False

-- The last commas, emptied before rule N (the parking comma: proof plan
-- §10, spike K1). The Rust P2 deletes a comma before a closer from the
-- text, and rule N runs again on what is left; running rule N first and
-- deleting the comma from the tree would leave a comment where the first
-- run parked it, which differs when the comma starts its line. Moving the
-- comma's comments first, and leaving it in bare, gives Rust's comments
-- from one parse.

def Leaf.startingLine (leaf: Leaf) (lineStart: Bool): Leaf := { leaf | token = { leaf.token | lineStart } }

--| Whether a comma may follow `behind`'s newest leaf as a last one: some
--| item must be before it (`[,]` has none).
def hasItem: List Leaf → Bool
  | [] => False
  | [leaf, ..rest] =>
    match leaf.kind with
      | Comma => False
      | Pipe => False
      | kind => !kind.isOpener

--| Whether `comma`, just older than a leaf of kind `above`, with `older`
--| behind it, is a last comma.
def lastPair (above: Tok) (comma: Leaf) (older: List Leaf): Bool :=
  comma.token.kind == Comma && above.isCloser && hasItem older

--| A last comma's comments moved as deleting the comma from the text moves
--| them: the closer after it, and `behind` (newest first), the leaves before
--| it. The comma's own-line comments go above the closer; its trailing
--| comment ends the line before it, or, if the comma started its line,
--| stands above the closer too, with the comma's blank line above it; a
--| comma that started its line, with no comment, leaves a blank line before
--| the closer's first own-line comment. Tokens are untouched.
def commaMoved (comma closer: Leaf) (behind: List Leaf): (Leaf, List Leaf) :=
  let starts := comma.token.lineStart
  let above := match comma.trivia.trailing with
    | Some comment if starts => comma.trivia.leading ++ [{ comment | blankLines = comma.trivia.blankLines }]
    | _ => comma.trivia.leading
  let kept := match comma.trivia.trailing, closer.trivia.leading with
    | None, [first, ..others] if starts => [{ first | blankLines = 1 }, ..others]
    | _, leading => leading
  let moved := closer.withLeading (above ++ kept)
  match comma.trivia.trailing, behind with
    | Some comment, [previous, ..earlier] if !starts => (moved, [previous.withTrailing (Some comment), ..earlier])
    | _, _ => (moved, behind)

--| A last comma deleted from the text: its comments moved (`commaMoved`),
--| and the closer after it starting the line if the comma did.
def commaDeleted (comma closer: Leaf) (behind: List Leaf): (Leaf, List Leaf) := (
  (commaMoved comma closer behind).fst.startingLine (comma.token.lineStart || closer.token.lineStart),
  (commaMoved comma closer behind).snd
)

--| The leaves without each comma directly before a closer (`commaDeleted`).
def withoutLastCommas (behind rest: List Leaf): List Leaf := match rest with
  | [] => behind.reverse
  | [comma, closer, ..after] if lastPair closer.token.kind comma behind =>
    let (moved, earlier) := commaDeleted comma closer behind
    withoutLastCommas [moved, ..earlier] after
  | [leaf, ..after] => withoutLastCommas [leaf, ..behind] after

--| The leaves with each comma directly before a closer kept but bare: its
--| comments moved as `withoutLastCommas` moves them, the comma left with
--| no comment and no blank line, still starting its line if it did. Every
--| token stays the lexer's. Rule N then treats the comma as if it weren't
--| there (a search found no case where it doesn't; its walk
--| reads the comma's line start as the closer's, `startsWalk`), and the
--| parser still reads it, so a file reads as the source does, commas and
--| all.
def withBareLastCommas (behind rest: List Leaf): List Leaf := match rest with
  | [] => behind.reverse
  | [comma, closer, ..after] if lastPair closer.token.kind comma behind =>
    let (moved, earlier) := commaMoved comma closer behind
    withBareLastCommas [moved, { comma | trivia = Trivia.empty }, ..earlier] after
  | [leaf, ..after] => withBareLastCommas [leaf, ..behind] after

--| Rule N after the last commas are taken out, as the Rust P2 leaves the
--| file's comments.
def Lexed.settledBare (lexed: Lexed): Lexed := { lexed | leaves = withoutLastCommas [] lexed.leaves }.settled

--| The leaves the formatter parses: rule N after the last commas are made
--| bare.
def Lexed.settledOnce (lexed: Lexed): Lexed := { lexed | leaves = withBareLastCommas [] lexed.leaves }.settledWith True
