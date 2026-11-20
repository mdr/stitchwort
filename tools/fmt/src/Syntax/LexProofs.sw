--| Proofs about the lexer (`Syntax/Lexer.sw`) for the alphabet of slice 1 of the proved formatter
--| (docs/proposals/self-hosted-fmt-s1-sketch.md, ticket 14).
--|
--| In layers, bottom up:
--|
--| 1. `item` reads one lexeme from a text that spells it and goes on with a character that doesn't extend it
--|    (`ItemReads`; `itemReadsColon`, `itemReadsWord`, `itemReadsNum`, … and `lexWord1` for all the kinds at once, by
--|    `Spells` and `MayFollow`).
--| 2. `many` over `item` and `recursiveWith`, for a source read lexeme by lexeme (`lexemesOfSteps`, `lexCovers`).
--| 3. `assemble`'s layout of pieces (`Laid`): columns in bytes, line starts, the comments and blank lines above each
--|    token (`lexPrinted`, `lexPieces`, `lexPrintedPairs`).
--| 4. One standalone read-back for each token kind (`lexesAs…`) and `operatorTokLexes`.

namespace Syntax.Proofs
import Std (Bool, Char, DecEq, Effect, Eq, byDecision, List, Nat, Option, Pair, Parse, Result, Text, Void)
import Syntax (..)
import Fmt (..)
import Syntax.SharedFacts (wordStartChar)

--| `text` is lexed as one token of `kind`, alone at the start of a line with no comments around it.
def LexesAs (text: Text) (kind: Tok): Prop :=
  lex text
    = Ok {
      leaves = [{ token = { kind, text, column = 0, lineStart = True }, trivia = Trivia.empty }],
      end = Trivia.empty
    }

--| `skip` reads exactly the characters it is asked for.
--|
--| Proof idea: Induction on the count: one `Parse.next` that accepts anything, then `skip` on the rest.
theorem runsSkip ∀ (count: Nat) (read rest: List Char)
    (counted: read.length = count):
    Parse.Runs (() => skip count) read rest () :=
  match count, read, counted with
    | Zero, [], counted => Parse.runsPure () rest
    | Zero, [first, ..others], counted => cases
    | Succ more, [], counted => cases
    | Succ more, [first, ..others], counted =>
      Parse.runsBind
        (() => Parse.next (char => True))
        (taken => skip more)
        [first]
        others
        [first, ..others]
        rest
        (Some first)
        ()
        byComputing
        (Parse.runsNext (char => True) first (others ++ rest) byComputing)
        (runsSkip more others rest (arithmetic [counted]))

--| A token of `count` characters, read from where `state` is.
--|
--| Proof idea: `tokenOf` is a mark, `skip`, then `located`: `runsSkip` for the middle, and the offsets add up because the second mark is `count` further on.
theorem runsFromTokenOf ∀ (state: Parse.State Char) (kind: Tok) (count: Nat) (read rest: List Char)
    (counted: read.length = count):
    Parse.RunsFrom state (() => tokenOf kind count) read rest {
      value = TokenLexeme kind,
      offset = state.at.offset,
      length = count
    } :=
  Parse.runsFromMark state
    (from =>
      let skipped := skip count
      located (TokenLexeme kind) from)
    read
    rest
    { value = TokenLexeme kind, offset = state.at.offset, length = count }
    (Parse.runsFromBind state
      (() => skip count)
      (skipped => located (TokenLexeme kind) state.at)
      read
      []
      read
      rest
      ()
      { value = TokenLexeme kind, offset = state.at.offset, length = count }
      (List.appendNil read).flipped
      (runsSkip count read rest counted)
      (middle atRest honest offset =>
        Parse.runsFromMark middle
          (finish =>
            ({
              value = TokenLexeme kind,
              offset = state.at.offset,
              length = finish.offset - state.at.offset
            }: Parse.Located Lexeme))
          []
          rest
          { value = TokenLexeme kind, offset = state.at.offset, length = count }
          (rewrite (arithmetic [offset, counted]: middle.at.offset - state.at.offset = count) then
            Parse.runsPure _ rest middle)))

--| One token lexeme, as a list.
--|
--| Proof idea: Sequence `tokenOf` with a function that makes the singleton; nothing more is read.
theorem runsFromTokenList ∀ (state: Parse.State Char) (kind: Tok) (count: Nat) (read rest: List Char)
    (counted: read.length = count):
    Parse.RunsFrom state (() => [tokenOf kind count]) read rest [
      { value = TokenLexeme kind, offset = state.at.offset, length = count }
    ] :=
  starts honest =>
    Parse.runsFromBindAt state
      (() => tokenOf kind count)
      (x => [x])
      read
      []
      read
      rest
      { value = TokenLexeme kind, offset = state.at.offset, length = count }
      [{ value = TokenLexeme kind, offset = state.at.offset, length = count }]
      (List.appendNil read).flipped
      (runsFromTokenOf state kind count read rest counted)
      (middle atRest honest1 offset =>
        Parse.runsPure [{ value = TokenLexeme kind, offset = state.at.offset, length = count }] rest middle)
      starts
      honest

--| One `item`'s lexeme at a place: it reads `read` and gives the one lexeme, whatever follows is `rest`.
def ItemReads (read: List Char) (lexeme: Lexeme) (rest: List Char): Prop :=
  ∀ (self: Place → {Parse Char} List (Parse.Located Lexeme)) (source: Text) (state: Parse.State
      Char) => Parse.RunsFrom state (() => item self source TopLevel) read rest [
    { value = lexeme, offset = state.at.offset, length = read.length }
  ]

--| The lexemes of steps (what each reads, and which it is), the first at `offset`, as one-item rounds.
def roundsAt (offset: Nat): (steps: List (List Char, Lexeme)) → List (List (Parse.Located Lexeme))
  | [] => []
  | [(read, lexeme), ..steps] =>
    [[{ value = lexeme, offset, length = read.length }], ..roundsAt (offset + read.length) steps]

--| What `many (item …)` goes through: each round reads a lexeme (never none), and the last round's `item` stops.
def ItemRounds (self: Place → {Parse Char} List (Parse.Located Lexeme)) (source: Text):
    (steps: List (List Char, Lexeme)) → (rest: List Char) → Prop
  | [], rest => Parse.Declines (() => item self source TopLevel) rest
  | [(read, lexeme), ..steps], rest =>
    read ≠ [] ∧ ItemReads read lexeme (Parse.joinReads steps ++ rest) ∧ ItemRounds self source steps rest

theorem roundsShort ∀ (self: Place → {Parse Char} List (Parse.Located Lexeme)) (source: Text)
    (steps: List (List Char, Lexeme)) (rest: List Char)
    (rounds: ItemRounds self source steps rest):
    steps.length ≤ (Parse.joinReads steps).length :=
  match steps, rounds with
    | [], rounds => byComputing
    | [(read, lexeme), ..steps], Both nonEmpty (Both reads later) =>
      match read with
        | [] => (nonEmpty byComputing).impossible
        | [char, ..more] =>
          let shorter := roundsShort self source steps rest later
          arithmetic [shorter, List.lengthAppend more (Parse.joinReads steps)]

--| `manyFrom` over `item`, from a state at its `before` mark with enough fuel, after `found`: it gives the rounds.
--|
--| Proof idea: Induction on the rounds, as `Parse.runsManyFrom` is, with each round's `ItemReads` taken at the state it starts from, so that the offsets in the lexemes follow the state's: the offset after a round is the offset before it plus what it read.
theorem runsItemsFrom ∀ (self: Place → {Parse Char} List (Parse.Located Lexeme)) (source: Text):
    ∀ (steps: List (List Char, Lexeme)) (rest: List Char) (fuel: Nat) (found: List
      (List (Parse.Located Lexeme))) => steps.length < fuel
      → ItemRounds self source steps rest
      → ∀ (state: Parse.State Char) => Parse.RunsFrom state
        (() => Parse.manyFrom fuel (() => item self source TopLevel) found state.at)
        (Parse.joinReads steps)
        rest
        (found.reverse ++ roundsAt state.at.offset steps)
  | steps, rest, Zero, found, enough, rounds, state, starts, honest => Void.impossible (arithmetic [enough])
  | [], rest, Succ more, found, enough, declines, state, starts, honest =>
    rewrite List.appendNil found.reverse then
      (Parse.runsFromBindAt state
            (() => Parse.optionalFrom state.at (() => item self source TopLevel))
            (found2 => Parse.manyRound more (() => item self source TopLevel) found state.at found2)
            []
            []
            []
            rest
            None
            found.reverse
            byComputing
            (Parse.declinesRuns (() => item self source TopLevel) rest declines state)
            (middle atRest honest2 offset => Parse.runsPure found.reverse rest middle)) starts honest
  | [(read, lexeme), ..steps], rest, Succ more, found, enough, Both nonEmpty
      (Both reads later), state, starts, honest =>
    let short: steps.length < more := arithmetic [enough]
    let value: found.reverse
      ++ [
        [{ value = lexeme, offset = state.at.offset, length = read.length }],
        ..roundsAt (state.at.offset + read.length) steps
      ]
      = [[{ value = lexeme, offset = state.at.offset, length = read.length }], ..found].reverse
        ++ roundsAt (state.at.offset + read.length) steps :=
      rewrite List.reverseCons [{ value = lexeme, offset = state.at.offset, length = read.length }] found,
          List.appendAssoc found.reverse
            [[{ value = lexeme, offset = state.at.offset, length = read.length }]]
            (roundsAt (state.at.offset + read.length) steps)
    rewrite value then
      (Parse.runsFromBindAt state
            (() => Parse.optionalFrom state.at (() => item self source TopLevel))
            (found2 => Parse.manyRound more (() => item self source TopLevel) found state.at found2)
            read
            (Parse.joinReads steps)
            (read ++ Parse.joinReads steps)
            rest
            (Some [{ value = lexeme, offset = state.at.offset, length = read.length }])
            ([[{ value = lexeme, offset = state.at.offset, length = read.length }], ..found].reverse
              ++ roundsAt (state.at.offset + read.length) steps)
            byComputing
            (Parse.runsFromOptionalOf state
              (() => item self source TopLevel)
              read
              (Parse.joinReads steps ++ rest) _
              (reads self source state))
            (middle atRest honest2 offset =>
              let advanced: state.at.offset < middle.at.offset := match read with
                | [] => (nonEmpty byComputing).impossible
                | [char, ..others] => arithmetic [offset]
              let same: roundsAt middle.at.offset steps = roundsAt (state.at.offset + read.length) steps :=
                rewrite offset
              rewrite <- same then
                Parse.runsFromManyRound state.at more
                  (() => item self source TopLevel)
                  found
                  [{ value = lexeme, offset = state.at.offset, length = read.length }]
                  middle
                  (Parse.joinReads steps)
                  rest
                  ([[{ value = lexeme, offset = state.at.offset, length = read.length }], ..found].reverse
                    ++ roundsAt middle.at.offset steps)
                  advanced
                  (runsItemsFrom self source steps rest more
                    [[{ value = lexeme, offset = state.at.offset, length = read.length }], ..found]
                    short
                    later
                    middle))) starts honest

theorem concatRounds ∀ (offset: Nat) (steps: List (List Char, Lexeme)):
    List.concat (roundsAt offset steps) = Parse.locatedSteps offset steps :=
  match steps with
    | [] => byComputing
    | [(read, lexeme), ..more] => rewrite concatRounds (offset + read.length) more

--| `many (item …)` from any state reads the rounds, with each lexeme's offset from the state's.
--|
--| Proof idea: `many` marks where it starts and gives `manyFrom` as many rounds of fuel as there are characters left, which is more than the rounds.
theorem runsItems ∀ (self: Place → {Parse Char} List (Parse.Located Lexeme)) (source: Text)
    (steps: List (List Char, Lexeme)) (rest: List Char)
    (rounds: ItemRounds self source steps rest) (state: Parse.State Char):
    Parse.RunsFrom state
      (() => Parse.many (() => item self source TopLevel))
      (Parse.joinReads steps)
      rest
      (roundsAt state.at.offset steps) :=
  starts honest =>
    let short := roundsShort self source steps rest rounds
    let lengths: state.at.rest.length = (Parse.joinReads steps).length + rest.length :=
      rewrite starts then List.lengthAppend (Parse.joinReads steps) rest
    Parse.runsFromMark state
      (at => Parse.manyFrom (at.left + 1) (() => item self source TopLevel) [] at)
      (Parse.joinReads steps)
      rest
      (roundsAt state.at.offset steps)
      (runsItemsFrom self source steps rest (state.at.left + 1) [] (arithmetic [short, lengths, honest]) rounds state)
      starts
      honest

--| The lexemes of a source read lexeme by lexeme to its end (`steps`, from the first character, none reading nothing):
--| the lexer's `lexemes` gives them, each at its offset. The statement `lexCovers` and `lexPrinted` stand on.
--|
--| Proof idea: `lexemes` runs `lexemesIn` from the start state. `recursiveWith` starts one level in with as much fuel as there are characters; at the top level its body is `many` of `item`, which doesn't call itself for a lexeme that has no `{` or text literal, so any nested parser serves (`ItemRounds` is for every `self`), and `concatRounds` joins the one-lexeme rounds.
theorem lexemesOfSteps ∀ (source: Text) (steps: List (List Char, Lexeme))
    (reads: source.toList = Parse.joinReads steps)
    (rounds: ∀ (self: Place → {Parse Char} List (Parse.Located Lexeme)) => ItemRounds self source steps []):
    lexemes source = Ok (Parse.locatedSteps 0 steps) :=
  let body := (self inner => Parse.many (() => item self source inner) |> List.concat)
  let runs: Parse.RunsFrom
    (Parse.State.start source.toList)
    (() => lexemesIn source TopLevel)
    source.toList
    []
    (Parse.locatedSteps 0 steps) :=
    Parse.runsFromMark
      (Parse.State.start source.toList)
      (at => Parse.recursiveWithFuel (at.left + 1) body TopLevel)
      source.toList
      []
      (Parse.locatedSteps 0 steps)
      (Parse.runsFromBindAt
        (Parse.State.start source.toList)
        (() =>
          Parse.many (() => item (inner => Parse.recursiveWithFuel (source.toList.length) body inner) source TopLevel))
        (x => List.concat x)
        (Parse.joinReads steps)
        []
        source.toList
        []
        (roundsAt 0 steps)
        (Parse.locatedSteps 0 steps)
        (rewrite reads then (List.appendNil (Parse.joinReads steps)).flipped)
        (runsItems
          (inner => Parse.recursiveWithFuel (source.toList.length) body inner)
          source
          steps
          []
          (rounds (inner => Parse.recursiveWithFuel (source.toList.length) body inner))
          (Parse.State.start source.toList))
        (middle atRest honest3 offset =>
          rewrite concatRounds 0 steps then Parse.runsPure (Parse.locatedSteps 0 steps) [] middle))
  rewrite Parse.runsFromRun (() => lexemesIn source TopLevel) source.toList (Parse.locatedSteps 0 steps) runs

-- Layout: what `Assembly.add` does for each kind of lexeme.

--| The bytes of UTF-8 a run of characters takes.
def utf8Chars: List Char → Nat
  | [] => 0
  | [char, ..more] => (Char.utf8 char).length + utf8Chars more

theorem utf8Sum ∀ (chars: List Char) (acc: Nat):
    (chars.map (char => (Char.utf8 char).length)).foldLeft acc Nat.add = acc + utf8Chars chars :=
  match chars with
    | [] => byComputing
    | [char, ..more] => rewrite utf8Sum more (acc + (Char.utf8 char).length) then arithmetic

theorem utf8OfList ∀ (chars: List Char): (Text.fromList chars).utf8Length = utf8Chars chars := utf8Sum chars 0

--| A run of ASCII characters takes a byte each.
theorem utf8OfAsciiRun ∀ (chars: List Char)
    (ascii: chars.all (char => char.toNat < 128) = True):
    utf8Chars chars = chars.length :=
  match chars, ascii with
    | [], ascii => byComputing
    | [first, ..more], ascii =>
      let small: ((first.toNat <= 127): Bool) = True := Bool.andLeft ascii
      let later: more.all (char => char.toNat <= 127) = True := Bool.andRight ascii
      rewrite Char.utf8LengthAscii first (arithmetic [small]), utf8OfAsciiRun more later

theorem afterLastBreakNone ∀ (chars: List Char) (acc: Option Nat)
    (none: acc = None)
    (noBreak: chars.all (char => char != '\n') = True):
    chars.foldLeft acc (after char =>
      if char == '\n' then Some 0 else after.map (bytes => bytes + (Char.utf8 char).length))
      = None :=
  match chars, noBreak with
    | [], noBreak => none
    | [char, ..more], noBreak =>
      let later: more.all (char => char != '\n') = True := Bool.andRight noBreak
      match same: char == '\n' with
        | False => afterLastBreakNone more (acc.map (bytes => bytes + (Char.utf8 char).length)) (rewrite none) later

theorem widthOfRun ∀ (read: List Char):
    (if read.all (char => char.toNat < 128) then read.length
     else (read.map (char => (Char.utf8 char).length)).foldLeft 0 Nat.add)
      = utf8Chars read :=
  match same: read.all (char => char.toNat < 128) with
    | True => (utf8OfAsciiRun read same).flipped
    | False => utf8Sum read 0

--| A token: its layout is where the line is, and it takes the comments and blank lines that waited for it.
--|
--| Proof idea: Unfold `Assembly.add` with the slice replaced by the characters read; a token with no line break leaves the line start where it was, and its width is its UTF-8 length (`widthOfRun`).
theorem addToken ∀ (assembly: Assembly) (source: Text) (offset: Nat) (read: List Char) (kind: Tok)
    (cut: (source.toList.drop offset).take (offset + read.length - offset) = read)
    (noBreak: read.all (char => char != '\n') = True):
    assembly.add source { value = TokenLexeme kind, offset, length = read.length }
      = {
        leaves = [
          {
            token = {
              kind,
              text = Text.fromList read,
              column = assembly.bytes - assembly.lineStart,
              lineStart = assembly.freshLine
            },
            trivia = { leading = assembly.pending.reverse, blankLines = assembly.blankRun, trailing = None }
          },
          ..assembly.leaves
        ],
        pending = [],
        blankRun = 0,
        lineBlank = False,
        freshLine = False,
        bytes = assembly.bytes + utf8Chars read,
        lineStart = assembly.lineStart
      } :=
  rewrite cut, afterLastBreakNone read None byComputing noBreak, widthOfRun read

theorem addSpaces ∀ (assembly: Assembly) (source: Text) (offset length: Nat):
    assembly.add source { value = Spaces, offset, length } = { assembly | bytes = assembly.bytes + length } :=
  byComputing

--| A line break ends the line, which was blank if nothing but spaces was on it.
theorem addBreak ∀ (assembly: Assembly) (source: Text) (offset: Nat):
    assembly.add source { value = LineBreak, offset, length = 1 }
      = { assembly |
        blankRun = if assembly.lineBlank then assembly.blankRun + 1 else assembly.blankRun,
        lineBlank = True,
        freshLine = True,
        bytes = assembly.bytes + 1,
        lineStart = assembly.bytes + 1
      } :=
  byComputing

-- Pieces: what a printer writes, and the leaves they make.

--| A piece of printed text: a token's spelling, spaces, a line break or a comment.
type Piece =
  | Code (kind: Tok) (text: Text)
  | Gap (count: Nat)
  | Break
  | Remark (text: Text)

def Piece.chars: Piece → List Char
  | Code _ text => text.toList
  | Gap count => List.replicate count ' '
  | Break => ['\n']
  | Remark text => text.toList

def Piece.lexeme: Piece → Lexeme
  | Code kind _ => TokenLexeme kind
  | Gap _ => Spaces
  | Break => LineBreak
  | Remark _ => CommentLexeme

--| What each piece reads, and which lexeme it is.
def pieceSteps: List Piece → List (List Char, Lexeme)
  | [] => []
  | [piece, ..more] => [(piece.chars, piece.lexeme), ..pieceSteps more]

--| A piece is the sort the lexer reads as one lexeme with the layout below: tokens and comments have no line break
--| and something in them, spaces are spaces, a break is `\n`.
def Piece.Plain: Piece → Prop
  | Code _ text => text.toList ≠ [] ∧ text.toList.all (char => char != '\n') = True
  | Gap count => count ≠ 0
  | Break => True
  | Remark text => text.toList ≠ [] ∧ text.toList.all (char => char != '\n') = True

def AllPlain: List Piece → Prop
  | [] => True
  | [piece, ..more] => piece.Plain ∧ AllPlain more

--| The layout so far, as the printer's author thinks of it: leaves made (newest first), comments waiting (newest
--| first), blank lines before them, whether the line has had only blanks, whether no token has started it, and
--| the column in bytes.
type Laid = {
  leaves: List Leaf,
  pending: List Comment,
  blankRun: Nat,
  lineBlank: Bool,
  freshLine: Bool,
  column: Nat
}

def Laid.start: Laid := { leaves = [], pending = [], blankRun = 0, lineBlank = True, freshLine = True, column = 0 }

def Laid.lay (laid: Laid): Piece → Laid
  | Code kind text => {
    leaves = [
      {
        token = { kind, text, column = laid.column, lineStart = laid.freshLine },
        trivia = { leading = laid.pending.reverse, blankLines = laid.blankRun, trailing = None }
      },
      ..laid.leaves
    ],
    pending = [],
    blankRun = 0,
    lineBlank = False,
    freshLine = False,
    column = laid.column + text.utf8Length
  }
  | Gap count => { laid | column = laid.column + count }
  | Break => { laid |
    blankRun = if laid.lineBlank then laid.blankRun + 1 else laid.blankRun,
    lineBlank = True,
    freshLine = True,
    column = 0
  }
  | Remark text =>
    let comment: Comment := { text = withoutReturn text, column = laid.column, blankLines = laid.blankRun }
    if laid.freshLine then
      { laid |
        pending = [comment, ..laid.pending],
        blankRun = 0,
        lineBlank = False,
        column = laid.column + text.utf8Length
      }
    else
      { laid | leaves = withTrailing laid.leaves { comment | blankLines = 0 }, column = laid.column + text.utf8Length }

--| An assembly in the layout `laid`, whose line began at byte `lineStart`.
def Assembly.of (laid: Laid) (lineStart: Nat): Assembly := {
  leaves = laid.leaves,
  pending = laid.pending,
  blankRun = laid.blankRun,
  lineBlank = laid.lineBlank,
  freshLine = laid.freshLine,
  bytes = lineStart + laid.column,
  lineStart
}

--| Where the line starts after a piece.
def nextLine (laid: Laid) (lineStart: Nat): Piece → Nat
  | Break => lineStart + laid.column + 1
  | _ => lineStart

theorem utf8OfText ∀ (text: Text): text.utf8Length = utf8Chars text.toList :=
  rewrite <- Text.fromToList text then utf8OfList text.toList

theorem addCode ∀ (laid: Laid) (lineStart: Nat) (source: Text) (offset: Nat) (kind: Tok) (text: Text)
    (cut: (source.toList.drop offset).take (offset + text.toList.length - offset) = text.toList)
    (noBreak: text.toList.all (char => char != '\n') = True):
    (Assembly.of laid lineStart).add source { value = TokenLexeme kind, offset, length = text.toList.length }
      = Assembly.of (laid.lay (Code kind text)) lineStart :=
  rewrite addToken (Assembly.of laid lineStart) source offset text.toList kind cut noBreak,
      Text.fromToList text,
      utf8OfText text,
      (arithmetic: lineStart + laid.column - lineStart = laid.column),
      (arithmetic: lineStart + laid.column + utf8Chars text.toList = lineStart + (laid.column + utf8Chars text.toList))

theorem addGap ∀ (laid: Laid) (lineStart: Nat) (source: Text) (offset count: Nat):
    (Assembly.of laid lineStart).add source { value = Spaces, offset, length = (List.replicate count ' ').length }
      = Assembly.of (laid.lay (Gap count)) lineStart :=
  rewrite addSpaces (Assembly.of laid lineStart) source offset (List.replicate count ' ').length,
      List.lengthReplicate ' ' count,
      (arithmetic: lineStart + laid.column + count = lineStart + (laid.column + count))

theorem addLineBreak ∀ (laid: Laid) (lineStart: Nat) (source: Text) (offset: Nat):
    (Assembly.of laid lineStart).add source { value = LineBreak, offset, length = 1 }
      = Assembly.of (laid.lay Break) (nextLine laid lineStart Break) :=
  rewrite addBreak (Assembly.of laid lineStart) source offset,
      (arithmetic: lineStart + laid.column + 1 + 0 = lineStart + laid.column + 1)

--| A comment, from its `--` to the end of the line: on a line of its own it waits for the next token, after a token it is that token's.
--|
--| Proof idea: Unfold `Assembly.add` with the slice replaced by the characters read, and `utf8Sum` for the width.
theorem addComment ∀ (assembly: Assembly) (source: Text) (offset: Nat) (read: List Char)
    (cut: (source.toList.drop offset).take (offset + read.length - offset) = read):
    assembly.add source { value = CommentLexeme, offset, length = read.length }
      = if assembly.freshLine then
        { assembly |
          pending = [
            {
              text = withoutReturn (Text.fromList read),
              column = assembly.bytes - assembly.lineStart,
              blankLines = assembly.blankRun
            },
            ..assembly.pending
          ],
          blankRun = 0,
          lineBlank = False,
          bytes = assembly.bytes + utf8Chars read
        }
      else
        { assembly |
          leaves = withTrailing assembly.leaves {
            text = withoutReturn (Text.fromList read),
            column = assembly.bytes - assembly.lineStart,
            blankLines = 0
          },
          bytes = assembly.bytes + utf8Chars read
        } :=
  rewrite cut, utf8Sum read 0

theorem addRemark ∀ (laid: Laid) (lineStart: Nat) (source: Text) (offset: Nat) (text: Text)
    (cut: (source.toList.drop offset).take (offset + text.toList.length - offset) = text.toList):
    (Assembly.of laid lineStart).add source { value = CommentLexeme, offset, length = text.toList.length }
      = Assembly.of (laid.lay (Remark text)) lineStart :=
  rewrite addComment (Assembly.of laid lineStart) source offset text.toList cut,
      utf8OfText text,
      Text.fromToList text,
      (arithmetic: lineStart + laid.column - lineStart = laid.column),
      (arithmetic: lineStart + laid.column + utf8Chars text.toList
        = lineStart + (laid.column + utf8Chars text.toList)) then
    match same: laid.freshLine with | True | False => byComputing

--| `Assembly.add` of a piece's lexeme makes the next layout.
theorem addPiece ∀ (laid: Laid) (lineStart: Nat) (source: Text) (offset: Nat) (piece: Piece)
    (cut: (source.toList.drop offset).take (offset + piece.chars.length - offset) = piece.chars) (plain: piece.Plain):
    (Assembly.of laid lineStart).add source { value = piece.lexeme, offset, length = piece.chars.length }
      = Assembly.of (laid.lay piece) (nextLine laid lineStart piece) :=
  match piece, plain with
    | Code kind text, Both nonEmpty noBreak => addCode laid lineStart source offset kind text cut noBreak
    | Gap count, plain => addGap laid lineStart source offset count
    | Break, plain => addLineBreak laid lineStart source offset
    | Remark text, Both nonEmpty noBreak => addRemark laid lineStart source offset text cut

--| The fold `assemble` makes over the lexemes of pieces, from layout `laid`: the layout the pieces make.
--|
--| Proof idea: Induction on the pieces: `addPiece` for the first, with the slice for its lexeme cut out of the source (`List.takeDropAppend`), then the rest from the layout it leaves, at the offset after it.
theorem foldPieces ∀ (source: Text) (pieces: List Piece) (before after: List Char) (laid: Laid) (lineStart: Nat)
    (made: source.toList = before ++ (Parse.joinReads (pieceSteps pieces) ++ after))
    (plain: AllPlain pieces):
    ∃ (end: Nat) => (Parse.locatedSteps before.length (pieceSteps pieces)).foldLeft
      (Assembly.of laid lineStart)
      (assembly lexeme => assembly.add source lexeme)
      = Assembly.of (pieces.foldLeft laid Laid.lay) end :=
  match pieces, plain with
    | [], plain => Witness lineStart byComputing
    | [piece, ..more], Both pieceOk moreOk =>
      let split: source.toList = before ++ (piece.chars ++ (Parse.joinReads (pieceSteps more) ++ after)) :=
        rewrite List.appendAssoc piece.chars (Parse.joinReads (pieceSteps more)) after at made then made
      let regrouped: source.toList = (before ++ piece.chars) ++ (Parse.joinReads (pieceSteps more) ++ after) :=
        rewrite List.appendAssoc before piece.chars (Parse.joinReads (pieceSteps more) ++ after) then split
      let step :=
        addPiece laid lineStart source before.length piece
          (rewrite (arithmetic: before.length + piece.chars.length - before.length = piece.chars.length) then
            List.takeDropAppend source.toList before piece.chars (Parse.joinReads (pieceSteps more) ++ after) split)
          pieceOk
      match foldPieces source more
        (before ++ piece.chars)
        after
        (laid.lay piece)
        (nextLine laid lineStart piece)
        regrouped
        moreOk with
        | Witness end ran =>
          Witness end (rewrite step then rewrite List.lengthAppend before piece.chars at ran then ran)

--| `lexPrinted`: pieces that the lexer reads lexeme by lexeme (each `ItemReads`, with what follows it) lex to the leaves
--| of the layout they make: each token with its column in bytes, whether it starts its line, and the comments and
--| blank lines above it; the comments and blank lines after the last token end the file.
--|
--| Proof idea: `lexemesOfSteps` gives the lexemes, `foldPieces` the fold of `assemble` over them from `Assembly.start`, which is the assembly of the empty layout.
theorem lexPrinted ∀ (source: Text) (pieces: List Piece)
    (reads: source.toList = Parse.joinReads (pieceSteps pieces))
    (rounds: ∀ (self: Place → {Parse Char} List (Parse.Located Lexeme)) => ItemRounds self source
      (pieceSteps pieces)
      [])
    (plain: AllPlain pieces):
    lex source
      = Ok {
        leaves = (pieces.foldLeft Laid.start Laid.lay).leaves.reverse,
        end = {
          leading = (pieces.foldLeft Laid.start Laid.lay).pending.reverse,
          blankLines = (pieces.foldLeft Laid.start Laid.lay).blankRun,
          trailing = None
        }
      } :=
  let made: source.toList = [] ++ (Parse.joinReads (pieceSteps pieces) ++ []) :=
    rewrite List.appendNil (Parse.joinReads (pieceSteps pieces)) then reads
  match foldPieces source pieces [] [] Laid.start 0 made plain with
    | Witness end ran => rewrite lexemesOfSteps source (pieceSteps pieces) reads rounds, ran

--| At the end of the input `item` stops, which is what ends the lexemes.
theorem declinesItemEnd ∀ (self: Place → {Parse Char} List (Parse.Located Lexeme)) (source: Text):
    Parse.Declines (() => item self source TopLevel) [] :=
  state starts honest => rewrite starts

--| What `item` does on `read` followed by `rest`, said of `itemOn` at the mark where it starts.
theorem itemReadsVia ∀ (read rest: List Char) (lexeme: Lexeme)
    (via: ∀ (self: Place → {Parse Char} List (Parse.Located Lexeme)) (source: Text) (state: Parse.State
        Char) => Parse.RunsFrom state (() => itemOn self source TopLevel state.at (read ++ rest)) read rest [
      { value = lexeme, offset = state.at.offset, length = read.length }
    ]):
    ItemReads read lexeme rest :=
  self source state =>
    Parse.runsFromMark state (from => itemOn self source TopLevel from from.rest) read rest _ (starts honest =>
      rewrite starts then via self source state starts honest)

-- Fixed spellings: each token's `item`, and what may follow it.

theorem itemReadsLParen ∀ (rest: List Char): ItemReads ['('] (TokenLexeme LParen) rest :=
  itemReadsVia ['('] rest (TokenLexeme LParen) (self source state =>
    runsFromTokenList state LParen 1 ['('] rest byComputing)

theorem itemReadsRParen ∀ (rest: List Char): ItemReads [')'] (TokenLexeme RParen) rest :=
  itemReadsVia [')'] rest (TokenLexeme RParen) (self source state =>
    runsFromTokenList state RParen 1 [')'] rest byComputing)

theorem itemReadsLBracket ∀ (rest: List Char): ItemReads ['['] (TokenLexeme LBracket) rest :=
  itemReadsVia ['['] rest (TokenLexeme LBracket) (self source state =>
    runsFromTokenList state LBracket 1 ['['] rest byComputing)

theorem itemReadsRBracket ∀ (rest: List Char): ItemReads [']'] (TokenLexeme RBracket) rest :=
  itemReadsVia [']'] rest (TokenLexeme RBracket) (self source state =>
    runsFromTokenList state RBracket 1 [']'] rest byComputing)

theorem itemReadsComma ∀ (rest: List Char): ItemReads [','] (TokenLexeme Comma) rest :=
  itemReadsVia [','] rest (TokenLexeme Comma) (self source state =>
    runsFromTokenList state Comma 1 [','] rest byComputing)
theorem itemReadsColon ∀ (rest: List Char) (follow: rest.head ≠ Some '='): ItemReads [':'] (TokenLexeme Colon) rest :=
  match rest, follow with
    | [], follow => itemReadsVia [':'] rest (TokenLexeme Colon) (self source state =>
      runsFromTokenList state Colon 1 [':'] rest byComputing)
    | [next, ..more], follow =>
      match next with
        | '=' => (follow byComputing).impossible
        | other => itemReadsVia [':'] rest (TokenLexeme Colon) (self source state =>
          runsFromTokenList state Colon 1 [':'] rest byComputing)

theorem itemReadsColonEq ∀ (rest: List Char): ItemReads [':', '='] (TokenLexeme ColonEq) rest :=
  itemReadsVia [':', '='] rest (TokenLexeme ColonEq) (self source state =>
    runsFromTokenList state ColonEq 2 [':', '='] rest byComputing)
theorem itemReadsEquals ∀ (rest: List Char)
    (follow: rest.head ≠ Some '=' ∧ rest.head ≠ Some '>'):
    ItemReads ['='] (TokenLexeme Equals) rest :=
  match rest, follow with
    | [], (Both first second) => itemReadsVia ['='] rest (TokenLexeme Equals) (self source state =>
      runsFromTokenList state Equals 1 ['='] rest byComputing)
    | [next, ..more], (Both first second) =>
      match next with
        | '=' => (first byComputing).impossible
        | '>' => (second byComputing).impossible
        | other => itemReadsVia ['='] rest (TokenLexeme Equals) (self source state =>
          runsFromTokenList state Equals 1 ['='] rest byComputing)

theorem itemReadsEqEq ∀ (rest: List Char): ItemReads ['=', '='] (TokenLexeme EqEq) rest :=
  itemReadsVia ['=', '='] rest (TokenLexeme EqEq) (self source state =>
    runsFromTokenList state EqEq 2 ['=', '='] rest byComputing)

theorem itemReadsArrow ∀ (rest: List Char): ItemReads ['-', '>'] (TokenLexeme Arrow) rest :=
  itemReadsVia ['-', '>'] rest (TokenLexeme Arrow) (self source state =>
    runsFromTokenList state Arrow 2 ['-', '>'] rest byComputing)

theorem itemReadsOrOr ∀ (rest: List Char): ItemReads ['|', '|'] (TokenLexeme OrOr) rest :=
  itemReadsVia ['|', '|'] rest (TokenLexeme OrOr) (self source state =>
    runsFromTokenList state OrOr 2 ['|', '|'] rest byComputing)

theorem itemReadsAndAnd ∀ (rest: List Char): ItemReads ['&', '&'] (TokenLexeme AndAnd) rest :=
  itemReadsVia ['&', '&'] rest (TokenLexeme AndAnd) (self source state =>
    runsFromTokenList state AndAnd 2 ['&', '&'] rest byComputing)
theorem itemReadsPlus ∀ (rest: List Char) (follow: rest.head ≠ Some '+'): ItemReads ['+'] (TokenLexeme Plus) rest :=
  match rest, follow with
    | [], follow => itemReadsVia ['+'] rest (TokenLexeme Plus) (self source state =>
      runsFromTokenList state Plus 1 ['+'] rest byComputing)
    | [next, ..more], follow =>
      match next with
        | '+' => (follow byComputing).impossible
        | other => itemReadsVia ['+'] rest (TokenLexeme Plus) (self source state =>
          runsFromTokenList state Plus 1 ['+'] rest byComputing)

theorem itemReadsPlusPlus ∀ (rest: List Char): ItemReads ['+', '+'] (TokenLexeme PlusPlus) rest :=
  itemReadsVia ['+', '+'] rest (TokenLexeme PlusPlus) (self source state =>
    runsFromTokenList state PlusPlus 2 ['+', '+'] rest byComputing)
theorem itemReadsMinus ∀ (rest: List Char)
    (follow: rest.head ≠ Some '-' ∧ rest.head ≠ Some '>'):
    ItemReads ['-'] (TokenLexeme Minus) rest :=
  match rest, follow with
    | [], (Both first second) => itemReadsVia ['-'] rest (TokenLexeme Minus) (self source state =>
      runsFromTokenList state Minus 1 ['-'] rest byComputing)
    | [next, ..more], (Both first second) =>
      match next with
        | '-' => (first byComputing).impossible
        | '>' => (second byComputing).impossible
        | other => itemReadsVia ['-'] rest (TokenLexeme Minus) (self source state =>
          runsFromTokenList state Minus 1 ['-'] rest byComputing)

theorem itemReadsStar ∀ (rest: List Char): ItemReads ['*'] (TokenLexeme Star) rest :=
  itemReadsVia ['*'] rest (TokenLexeme Star) (self source state =>
    runsFromTokenList state Star 1 ['*'] rest byComputing)

theorem itemReadsSlash ∀ (rest: List Char): ItemReads ['/'] (TokenLexeme Slash) rest :=
  itemReadsVia ['/'] rest (TokenLexeme Slash) (self source state =>
    runsFromTokenList state Slash 1 ['/'] rest byComputing)

theorem itemReadsPercent ∀ (rest: List Char): ItemReads ['%'] (TokenLexeme Percent) rest :=
  itemReadsVia ['%'] rest (TokenLexeme Percent) (self source state =>
    runsFromTokenList state Percent 1 ['%'] rest byComputing)

theorem itemReadsNotEq ∀ (rest: List Char): ItemReads ['!', '='] (TokenLexeme NotEq) rest :=
  itemReadsVia ['!', '='] rest (TokenLexeme NotEq) (self source state =>
    runsFromTokenList state NotEq 2 ['!', '='] rest byComputing)
theorem itemReadsLt ∀ (rest: List Char)
    (follow: rest.head ≠ Some '=' ∧ rest.head ≠ Some '-'):
    ItemReads ['<'] (TokenLexeme Lt) rest :=
  match rest, follow with
    | [], (Both first second) => itemReadsVia ['<'] rest (TokenLexeme Lt) (self source state =>
      runsFromTokenList state Lt 1 ['<'] rest byComputing)
    | [next, ..more], (Both first second) =>
      match next with
        | '=' => (first byComputing).impossible
        | '-' => (second byComputing).impossible
        | other => itemReadsVia ['<'] rest (TokenLexeme Lt) (self source state =>
          runsFromTokenList state Lt 1 ['<'] rest byComputing)

theorem itemReadsLe ∀ (rest: List Char): ItemReads ['<', '='] (TokenLexeme Le) rest :=
  itemReadsVia ['<', '='] rest (TokenLexeme Le) (self source state =>
    runsFromTokenList state Le 2 ['<', '='] rest byComputing)
theorem itemReadsGt ∀ (rest: List Char) (follow: rest.head ≠ Some '='): ItemReads ['>'] (TokenLexeme Gt) rest :=
  match rest, follow with
    | [], follow => itemReadsVia ['>'] rest (TokenLexeme Gt) (self source state =>
      runsFromTokenList state Gt 1 ['>'] rest byComputing)
    | [next, ..more], follow =>
      match next with
        | '=' => (follow byComputing).impossible
        | other => itemReadsVia ['>'] rest (TokenLexeme Gt) (self source state =>
          runsFromTokenList state Gt 1 ['>'] rest byComputing)

theorem itemReadsGe ∀ (rest: List Char): ItemReads ['>', '='] (TokenLexeme Ge) rest :=
  itemReadsVia ['>', '='] rest (TokenLexeme Ge) (self source state =>
    runsFromTokenList state Ge 2 ['>', '='] rest byComputing)
--| A `!` before anything but `=` or the word `in` is read alone: the lexer reads `!=` and `!in` (with no more of a
--| name after it) as longer tokens.
theorem itemReadsBang ∀ (rest: List Char)
    (follow: rest.head ≠ Some '=' ∧ rest.takeWhile isWordChar ≠ ['i', 'n']):
    ItemReads ['!'] (TokenLexeme Bang) rest :=
  match rest, follow with
    | [], (Both first second) => itemReadsVia ['!'] rest (TokenLexeme Bang) (self source state =>
      runsFromTokenList state Bang 1 ['!'] rest byComputing)
    | [next, ..more], (Both first second) =>
      match next with
        | '=' => (first byComputing).impossible
        | 'i' =>
          match more with
            | [] => itemReadsVia ['!'] rest (TokenLexeme Bang) (self source state =>
              runsFromTokenList state Bang 1 ['!'] rest byComputing)
            | [after, ..later] =>
              match after with
                | 'n' =>
                  match later with
                    | [] => (second byComputing).impossible
                    | [third, ..rest3] =>
                      match word: isWordChar third with
                        | True => itemReadsVia ['!'] rest (TokenLexeme Bang) (self source state =>
                          runsFromTokenList state Bang 1 ['!'] rest byComputing)
                        | False => (second byComputing).impossible
                | other => itemReadsVia ['!'] rest (TokenLexeme Bang) (self source state =>
                  runsFromTokenList state Bang 1 ['!'] rest byComputing)
        | other => itemReadsVia ['!'] rest (TokenLexeme Bang) (self source state =>
          runsFromTokenList state Bang 1 ['!'] rest byComputing)

theorem itemReadsArrowUnicode ∀ (rest: List Char): ItemReads ['→'] (TokenLexeme Arrow) rest :=
  itemReadsVia ['→'] rest (TokenLexeme Arrow) (self source state =>
    runsFromTokenList state Arrow 1 ['→'] rest byComputing)

theorem itemReadsAndAndUnicode ∀ (rest: List Char): ItemReads ['∧'] (TokenLexeme AndAnd) rest :=
  itemReadsVia ['∧'] rest (TokenLexeme AndAnd) (self source state =>
    runsFromTokenList state AndAnd 1 ['∧'] rest byComputing)

theorem itemReadsOrOrUnicode ∀ (rest: List Char): ItemReads ['∨'] (TokenLexeme OrOr) rest :=
  itemReadsVia ['∨'] rest (TokenLexeme OrOr) (self source state =>
    runsFromTokenList state OrOr 1 ['∨'] rest byComputing)

theorem itemReadsBangUnicode ∀ (rest: List Char): ItemReads ['¬'] (TokenLexeme Bang) rest :=
  itemReadsVia ['¬'] rest (TokenLexeme Bang) (self source state =>
    runsFromTokenList state Bang 1 ['¬'] rest byComputing)

theorem itemReadsLeUnicode ∀ (rest: List Char): ItemReads ['≤'] (TokenLexeme Le) rest :=
  itemReadsVia ['≤'] rest (TokenLexeme Le) (self source state => runsFromTokenList state Le 1 ['≤'] rest byComputing)

theorem itemReadsGeUnicode ∀ (rest: List Char): ItemReads ['≥'] (TokenLexeme Ge) rest :=
  itemReadsVia ['≥'] rest (TokenLexeme Ge) (self source state => runsFromTokenList state Ge 1 ['≥'] rest byComputing)

theorem itemReadsNotEqUnicode ∀ (rest: List Char): ItemReads ['≠'] (TokenLexeme NotEq) rest :=
  itemReadsVia ['≠'] rest (TokenLexeme NotEq) (self source state =>
    runsFromTokenList state NotEq 1 ['≠'] rest byComputing)

--| A lexeme made as `item` makes the spaces, line breaks and comments: something read, then the lexeme located from
--| where the item began.
--|
--| Proof idea: Sequence the reading with the `located`: its length is the offset of the mark after the reading minus the one before, which is the length of what was read.
theorem runsFromThenLocated ∀ (state: Parse.State Char) (p: () → {Parse Char} a) (read rest: List Char)
    (v: a) (value: Lexeme)
    (runs: Parse.Runs p read rest v):
    Parse.RunsFrom state
      (() =>
        let done := p()
        [located value state.at])
      read
      rest
      [{ value, offset = state.at.offset, length = read.length }] :=
  Parse.runsFromBind state p
    (done => [located value state.at])
    read
    []
    read
    rest
    v
    [{ value, offset = state.at.offset, length = read.length }]
    (List.appendNil read).flipped
    runs
    (middle atRest honest offset =>
      Parse.runsFromMark middle
        (finish =>
          [({ value, offset = state.at.offset, length = finish.offset - state.at.offset }: Parse.Located Lexeme)])
        []
        rest
        [{ value, offset = state.at.offset, length = read.length }]
        (rewrite (arithmetic [offset]: middle.at.offset - state.at.offset = read.length) then
          Parse.runsPure [{ value, offset = state.at.offset, length = read.length }] rest middle))

-- Spaces, line breaks and comments.

theorem itemReadsBreak ∀ (rest: List Char): ItemReads ['\n'] LineBreak rest :=
  itemReadsVia ['\n'] rest LineBreak (self source state =>
    runsFromThenLocated state (() => skip 1) ['\n'] rest () LineBreak (runsSkip 1 ['\n'] rest byComputing))

theorem spacesPass ∀ (count: Nat): (List.replicate count ' ').all (char => char == ' ' || char == '\r') = True :=
  match count with
    | Zero => byComputing
    | Succ more => spacesPass more

theorem spacesStop ∀ (rest: List Char)
    (follow: rest.head ≠ Some ' ' ∧ rest.head ≠ Some '\r'):
    rest.takeWhile (char => char == ' ' || char == '\r') = [] :=
  match rest, follow with
    | [], follow => byComputing
    | [next, ..more], Both space carriage =>
      rewrite List.beqFalseOfHeadNe next more ' ' space, List.beqFalseOfHeadNe next more '\r' carriage

--| A run of spaces up to a character that isn't a space or a carriage return.
--|
--| Proof idea: `item` on a space reads `span` of spaces and carriage returns, which takes the whole run (`runsSpan`) and stops where the next character isn't one.
theorem itemReadsSpaces ∀ (count: Nat) (rest: List Char)
    (positive: count ≠ 0)
    (follow: rest.head ≠ Some ' ' ∧ rest.head ≠ Some '\r'):
    ItemReads (List.replicate count ' ') Spaces rest :=
  match count, positive with
    | Zero, positive => (positive byComputing).impossible
    | Succ more, positive => itemReadsVia (List.replicate (Succ more) ' ') rest Spaces (self source state =>
      runsFromThenLocated state
        (() => Parse.span (char => char == ' ' || char == '\r'))
        (List.replicate (Succ more) ' ')
        rest
        (List.replicate (Succ more) ' ')
        Spaces
        (Parse.runsSpan
          (char => char == ' ' || char == '\r')
          (List.replicate (Succ more) ' ')
          rest
          (spacesPass (Succ more))
          (spacesStop rest follow)))

--| A comment, from its `--` to the end of the line, in `item` at the top level.
--|
--| Proof idea: `span` of everything but a line break reads the whole comment (`runsSpan`); the `${…}` cases of the match are for another place, so the last arm gives the lexeme.
theorem itemReadsComment ∀ (others rest: List Char)
    (oneLine: others.all (char => char != '\n') = True)
    (ends: rest.takeWhile (char => char != '\n') = []):
    ItemReads ['-', '-', ..others] CommentLexeme rest :=
  itemReadsVia ['-', '-', ..others] rest CommentLexeme (self source state =>
    Parse.runsFromBind state
      (() => Parse.span (char => char != '\n'))
      (text =>
        match TopLevel, Parse.mark().rest with
          | Inside True _, ['\n', .._] => fail commentTakesBrace
          | Inside True _, [] => fail unclosedInterpolation
          | _, _ => [located CommentLexeme state.at])
      ['-', '-', ..others]
      []
      ['-', '-', ..others]
      rest
      ['-', '-', ..others]
      [{ value = CommentLexeme, offset = state.at.offset, length = ['-', '-', ..others].length }]
      (List.appendNil ['-', '-', ..others]).flipped
      (Parse.runsSpan (char => char != '\n') ['-', '-', ..others] rest oneLine ends)
      (middle atRest honest offset =>
        Parse.runsFromMark middle
          (finish =>
            match TopLevel, finish.rest with
              | Inside True _, ['\n', .._] => fail commentTakesBrace
              | Inside True _, [] => fail unclosedInterpolation
              | _, _ => [located CommentLexeme state.at])
          []
          rest
          [{ value = CommentLexeme, offset = state.at.offset, length = ['-', '-', ..others].length }]
          (Parse.runsFromMark middle
            (to =>
              [
                ({
                  value = CommentLexeme,
                  offset = state.at.offset,
                  length = to.offset - state.at.offset
                }: Parse.Located Lexeme)
              ])
            []
            rest
            [{ value = CommentLexeme, offset = state.at.offset, length = ['-', '-', ..others].length }]
            (rewrite (arithmetic [offset]: middle.at.offset - state.at.offset = ['-', '-', ..others].length) then
              Parse.runsPure
                [{ value = CommentLexeme, offset = state.at.offset, length = ['-', '-', ..others].length }]
                rest
                middle))))

-- Words.

--| `located` after something read: the lexeme at where the item began.
--|
--| Proof idea: `located` marks the end: its length is the offset there minus the start's.
theorem runsFromLocatedAfter ∀ (state middle: Parse.State Char) (value: Lexeme) (read rest: List Char)
    (atRest: middle.at.rest = rest)
    (honest: middle.at.left = middle.at.rest.length)
    (offset: middle.at.offset = state.at.offset + read.length):
    Parse.RunsFrom middle (() => located value state.at) [] rest {
      value,
      offset = state.at.offset,
      length = read.length
    } :=
  Parse.runsFromMark middle
    (finish => ({ value, offset = state.at.offset, length = finish.offset - state.at.offset }: Parse.Located Lexeme))
    []
    rest
    { value, offset = state.at.offset, length = read.length }
    (rewrite (arithmetic [offset]: middle.at.offset - state.at.offset = read.length) then
      Parse.runsPure { value, offset = state.at.offset, length = read.length } rest middle)

--| A qualified name doesn't go on after a text that doesn't start with a `.`.
theorem runsQualifiedNone ∀ (fuel: Nat) (upper: Bool) (rest: List Char)
    (noDot: rest.head ≠ Some '.'):
    Parse.Runs (() => qualified (Succ fuel) upper None) [] rest None :=
  state =>
    Parse.runsFromMark state (at => qualifiedOn fuel upper None at.rest) [] rest None (starts honest =>
      rewrite starts then
        match rest, noDot with
          | [], noDot => Parse.runsPure None [] state starts honest
          | [next, ..more], noDot =>
            match next with
              | '.' => (noDot byComputing).impossible
              | other => Parse.runsPure None [other, ..more] state starts honest)

--| `word`: a run of word characters, which isn't a qualified name, as the kind says.
--|
--| Proof idea: `span` reads the run (`runsSpan`); the look-ahead for a qualified name reads nothing, since no `.` follows (`runsQualifiedNone`), so the kind is `wordKind`'s of the text; then `located`.
theorem runsFromWordKind ∀ (state: Parse.State Char) (first: Char) (others rest: List Char)
    (word: others.all isWordChar = True)
    (starts: isWordStart first = True)
    (ends: rest.takeWhile isWordChar = [])
    (noDot: rest.head ≠ Some '.'):
    Parse.RunsFrom state (() => Syntax.word False) [first, ..others] rest {
      value = TokenLexeme (wordKind False (Text.fromList [first, ..others])),
      offset = state.at.offset,
      length = [first, ..others].length
    } :=
  let read := [first, ..others]
  let value: Parse.Located Lexeme :=
    { value = TokenLexeme (wordKind False (Text.fromList read)), offset = state.at.offset, length = read.length }
  Parse.runsFromMark state
    (wordFrom False)
    read
    rest
    value
    (Parse.runsFromBind state
      (() => Parse.span isWordChar)
      (taken =>
        let firstUpper := taken.head.map (char => char.isAsciiUppercase) |> .getOrElse False
        let kind := match qualified (state.at.left + 1) firstUpper None with
          | Some lastUpper => if lastUpper then Upper else Lower
          | None => wordKind False (Text.fromList taken)
        located (TokenLexeme kind) state.at)
      read
      []
      read
      rest
      read
      value
      (List.appendNil read).flipped
      (Parse.runsSpan isWordChar read rest (Bool.andIntro (wordStartChar first starts) word) ends)
      (middle atRest honest offset =>
        Parse.runsFromBind middle
          (() =>
            match qualified (state.at.left + 1) (first.isAsciiUppercase) None with
              | Some lastUpper => if lastUpper then Upper else Lower
              | None => wordKind False (Text.fromList read))
          (kind => located (TokenLexeme kind) state.at)
          []
          []
          []
          rest
          (wordKind False (Text.fromList read))
          value
          byComputing
          (Parse.runsBind
            (() => qualified (state.at.left + 1) (first.isAsciiUppercase) None)
            (found =>
              match found with
                | Some lastUpper => if lastUpper then Upper else Lower
                | None => wordKind False (Text.fromList read))
            []
            []
            []
            rest
            None
            (wordKind False (Text.fromList read))
            byComputing
            (runsQualifiedNone state.at.left first.isAsciiUppercase rest noDot)
            (Parse.runsPure (wordKind False (Text.fromList read)) rest))
          (middle2 atRest2 honest2 offset2 =>
            runsFromLocatedAfter state middle2
              (TokenLexeme (wordKind False (Text.fromList read)))
              read
              rest
              atRest2
              honest2
              (arithmetic [offset, offset2]))))

theorem runsFromWord ∀ (state: Parse.State Char) (first: Char) (others rest: List Char) (kind: Tok)
    (word: others.all isWordChar = True)
    (starts: isWordStart first = True)
    (ends: rest.takeWhile isWordChar = [])
    (noDot: rest.head ≠ Some '.')
    (kinded: wordKind False (Text.fromList [first, ..others]) = kind):
    Parse.RunsFrom state (() => Syntax.word False) [first, ..others] rest {
      value = TokenLexeme kind,
      offset = state.at.offset,
      length = [first, ..others].length
    } :=
  rewrite <- kinded then runsFromWordKind state first others rest word starts ends noDot

--| `word`, as the one-item list `item` gives.
--|
--| Proof idea: `runsFromWord` and a singleton.
theorem runsFromWordList ∀ (state: Parse.State Char) (first: Char) (others rest: List Char) (kind: Tok)
    (word: others.all isWordChar = True)
    (starts: isWordStart first = True)
    (ends: rest.takeWhile isWordChar = [])
    (noDot: rest.head ≠ Some '.')
    (kinded: wordKind False (Text.fromList [first, ..others]) = kind):
    Parse.RunsFrom state (() => [Syntax.word False]) [first, ..others] rest [
      { value = TokenLexeme kind, offset = state.at.offset, length = [first, ..others].length }
    ] :=
  Parse.runsFromBindAt state
    (() => Syntax.word False)
    (x => [x])
    [first, ..others]
    []
    [first, ..others]
    rest
    { value = TokenLexeme kind, offset = state.at.offset, length = [first, ..others].length }
    [{ value = TokenLexeme kind, offset = state.at.offset, length = [first, ..others].length }]
    (List.appendNil [first, ..others]).flipped
    (runsFromWord state first others rest kind word starts ends noDot kinded)
    (middle atRest honest offset =>
      Parse.runsPure
        [{ value = TokenLexeme kind, offset = state.at.offset, length = [first, ..others].length }]
        rest
        middle)

--| A name or keyword: word characters up to one that isn't, which isn't a `.` (so it isn't qualified).
--|
--| Proof idea: `item` tries the other lexemes first, each on a first character that a word start isn't (ten literal cases), then `isWordStart` holds and the word is read (`runsFromWordList`).
theorem itemReadsWord ∀ (first: Char) (others rest: List Char) (kind: Tok)
    (starts: isWordStart first = True)
    (word: others.all isWordChar = True)
    (ends: rest.takeWhile isWordChar = [])
    (noDot: rest.head ≠ Some '.')
    (kinded: wordKind False (Text.fromList [first, ..others]) = kind):
    ItemReads [first, ..others] (TokenLexeme kind) rest :=
  match first, starts with
    | '\n' | '}' | '{' | ' ' | '\r' | '\t' | '-' | '"' | '\'' | '.', starts => (Bool.falseNotTrue starts).impossible
    | other, starts => itemReadsVia [other, ..others] rest (TokenLexeme kind) (self source state =>
      starts2 honest =>
        rewrite starts then runsFromWordList state other others rest kind word starts ends noDot kinded starts2 honest)

-- Qualified names.

--| A qualified name's components after the first: each a `.`, a letter and word characters.
def qualChars: List (Pair Char (List Char)) → List Char
  | [] => []
  | [(letter, word), ..more] => ['.', letter, ..word] ++ qualChars more

--| The components are as the lexer reads them: each follows one that starts upper case.
def QualTail: Bool → List (Pair Char (List Char)) → Prop
  | _, [] => True
  | upper, [(letter, word), ..more] =>
    upper = True ∧ letter.isAsciiLetter = True ∧ word.all isWordChar = True ∧ QualTail letter.isAsciiUppercase more

--| What `qualified` gives after the components, from `found` before them.
def qualFound (found: Option Bool): List (Pair Char (List Char)) → Option Bool
  | [] => found
  | [(letter, _), ..more] => qualFound (Some letter.isAsciiUppercase) more

--| Whether the last component starts upper case, `last` if there is none.
def qualLast (last: Bool): List (Pair Char (List Char)) → Bool
  | [] => last
  | [(letter, _), ..more] => qualLast letter.isAsciiUppercase more

theorem qualFoundSome ∀ (last: Bool) (comps: List (Pair Char (List Char))):
    qualFound (Some last) comps = Some (qualLast last comps) :=
  match comps with
    | [] => byComputing
    | [(letter, word), ..more] => qualFoundSome letter.isAsciiUppercase more

--| A name's word characters end where a qualified name's next component starts, or where the text ends.
theorem qualCharsStops ∀ (comps: List (Pair Char (List Char))) (rest: List Char)
    (ends: rest.takeWhile isWordChar = []):
    (qualChars comps ++ rest).takeWhile isWordChar = [] :=
  match comps with
    | [] => ends
    | [(letter, word), ..more] => byComputing

theorem qualCharsLength ∀ (comps: List (Pair Char (List Char))): comps.length ≤ (qualChars comps).length :=
  match comps with
    | [] => byComputing
    | [(letter, word), ..more] =>
      let ih := qualCharsLength more
      arithmetic [ih, List.lengthAppend ['.', letter, ..word] (qualChars more)]

--| `qualified` with no `.` and letter next stops, giving what it has found.
theorem runsQualifiedStop ∀ (fuel: Nat) (upper: Bool) (found: Option Bool) (rest: List Char)
    (noDot: rest.head ≠ Some '.'):
    Parse.Runs (() => qualified (Succ fuel) upper found) [] rest found :=
  state =>
    Parse.runsFromMark state (at => qualifiedOn fuel upper found at.rest) [] rest found (starts honest =>
      rewrite starts then
        match rest, noDot with
          | [], noDot => Parse.runsPure found [] state starts honest
          | [next, ..more], noDot =>
            match next with
              | '.' => (noDot byComputing).impossible
              | other => Parse.runsPure found [other, ..more] state starts honest)

--| The components of a qualified name, read from `.`, one component at a time, as far as the fuel goes.
--|
--| Proof idea: Induction on the components: `qualifiedOn` sees `.` and a letter after a name that starts upper case,
--| skips the `.`, takes the word characters (`runsSpan`) and goes on with one less fuel.
theorem runsQualified ∀ (fuel: Nat) (upper: Bool) (found: Option Bool)
    (comps: List (Pair Char (List Char))) (rest: List Char)
    (ends: rest.takeWhile isWordChar = [])
    (noDot: rest.head ≠ Some '.')
    (tail: QualTail upper comps)
    (enough: comps.length < fuel):
    Parse.Runs (() => qualified fuel upper found) (qualChars comps) rest (qualFound found comps) :=
  match fuel, comps, tail, enough with
    | Zero, comps, tail, enough => (arithmetic [enough]: Void).impossible
    | Succ more, [], tail, enough => runsQualifiedStop more upper found rest noDot
    | Succ more, [(letter, word), ..others], Both isUpper (Both isLetter (Both isWord next)), enough => state =>
      Parse.runsFromMark state
        (at => qualifiedOn more upper found at.rest)
        (['.', letter, ..word] ++ qualChars others)
        rest
        (qualFound found [(letter, word), ..others])
        (starts honest =>
          rewrite starts, isUpper, isLetter then
            (Parse.runsBind
                  (() => skip 1)
                  (skipped =>
                    let component := Parse.span isWordChar
                    qualified more letter.isAsciiUppercase (Some letter.isAsciiUppercase))
                  ['.']
                  ([letter, ..word] ++ qualChars others)
                  (['.', letter, ..word] ++ qualChars others)
                  rest
                  ()
                  (qualFound found [(letter, word), ..others])
                  byComputing
                  (runsSkip 1 ['.'] (([letter, ..word] ++ qualChars others) ++ rest) byComputing)
                  (Parse.runsBind
                    (() => Parse.span isWordChar)
                    (component => qualified more letter.isAsciiUppercase (Some letter.isAsciiUppercase))
                    [letter, ..word]
                    (qualChars others)
                    ([letter, ..word] ++ qualChars others)
                    rest
                    [letter, ..word]
                    (qualFound found [(letter, word), ..others])
                    byComputing
                    (Parse.runsSpan isWordChar
                      [letter, ..word]
                      (qualChars others ++ rest)
                      (Bool.andIntro (letterWordChar letter isLetter) isWord)
                      (qualCharsStops others rest ends))
                    (runsQualified more letter.isAsciiUppercase
                      (Some letter.isAsciiUppercase)
                      others
                      rest
                      ends
                      noDot
                      next
                      (arithmetic [enough])))) state starts honest)

theorem letterWordChar ∀ (char: Char) (letter: char.isAsciiLetter = True): isWordChar char = True := arithmetic [letter]

--| The kind a qualified name's last component gives reads nothing.
theorem runsPureKind ∀ (lastUpper: Bool) (rest: List Char):
    Parse.Runs (() => if lastUpper then Upper else Lower) [] rest (if lastUpper then Upper else Lower) :=
  match lastUpper with
    | True => Parse.runsPure Upper rest
    | False => Parse.runsPure Lower rest

--| A qualified name is one token: the first component's word characters, then the components, whose last decides
--| the kind.
--|
--| Proof idea: As `runsFromWordKind`, with the look-ahead for a qualified name reading the components
--| (`runsQualified`) and giving the last one's case.
theorem runsFromWordQualified ∀ (state: Parse.State Char) (first: Char) (others rest: List Char)
    (comps: List (Pair Char (List Char))) (lastUpper: Bool)
    (word: others.all isWordChar = True)
    (starts: isWordStart first = True)
    (ends: rest.takeWhile isWordChar = [])
    (noDot: rest.head ≠ Some '.')
    (tail: QualTail first.isAsciiUppercase comps)
    (found: qualFound None comps = Some lastUpper):
    Parse.RunsFrom state (() => Syntax.word False) ([first, ..others] ++ qualChars comps) rest {
      value = TokenLexeme (if lastUpper then Upper else Lower),
      offset = state.at.offset,
      length = ([first, ..others] ++ qualChars comps).length
    } :=
  let read := [first, ..others] ++ qualChars comps
  let value: Parse.Located Lexeme :=
    { value = TokenLexeme (if lastUpper then Upper else Lower), offset = state.at.offset, length = read.length }
  Parse.runsFromMark state (wordFrom False) read rest value (starts1 honest1 =>
    (Parse.runsFromBind state
          (() => Parse.span isWordChar)
          (taken =>
            let firstUpper := taken.head.map (char => char.isAsciiUppercase) |> .getOrElse False
            let kind2 := match qualified (state.at.left + 1) firstUpper None with
              | Some lastUpper => if lastUpper then Upper else Lower
              | None => wordKind False (Text.fromList taken)
            located (TokenLexeme kind2) state.at)
          [first, ..others]
          (qualChars comps)
          read
          rest
          [first, ..others]
          value
          byComputing
          (Parse.runsSpan isWordChar
            [first, ..others]
            (qualChars comps ++ rest)
            (Bool.andIntro (wordStartChar first starts) word)
            (qualCharsStops comps rest ends))
          (middle atRest honest offset =>
            Parse.runsFromBind middle
              (() =>
                match qualified (state.at.left + 1) (first.isAsciiUppercase) None with
                  | Some lastUpper => if lastUpper then Upper else Lower
                  | None => wordKind False (Text.fromList [first, ..others]))
              (kind3 => located (TokenLexeme kind3) state.at)
              (qualChars comps)
              []
              (qualChars comps)
              rest
              (if lastUpper then Upper else Lower)
              value
              (List.appendNil (qualChars comps)).flipped
              (Parse.runsBind
                (() => qualified (state.at.left + 1) (first.isAsciiUppercase) None)
                (found =>
                  match found with
                    | Some lastUpper => if lastUpper then Upper else Lower
                    | None => wordKind False (Text.fromList [first, ..others]))
                (qualChars comps)
                []
                (qualChars comps)
                rest
                (Some lastUpper)
                (if lastUpper then Upper else Lower)
                (List.appendNil (qualChars comps)).flipped
                (rewrite found at runsQualified
                  (state.at.left + 1)
                  first.isAsciiUppercase
                  None
                  comps
                  rest
                  ends
                  noDot
                  tail
                  (arithmetic [
                    qualCharsLength comps,
                    honest1,
                    Eq.cong List.length starts1,
                    List.lengthAppend read rest,
                    List.lengthAppend [first, ..others] (qualChars comps)
                  ]))
                (runsPureKind lastUpper rest))
              (middle2 atRest2 honest2 offset2 =>
                runsFromLocatedAfter state middle2
                  (TokenLexeme (if lastUpper then Upper else Lower))
                  read
                  rest
                  atRest2
                  honest2
                  (arithmetic [offset, offset2, List.lengthAppend [first, ..others] (qualChars comps)])))) starts1
        honest1)

--| `word`, as the one-item list `item` gives.
theorem runsFromWordQualifiedList ∀ (state: Parse.State Char) (first: Char) (others rest: List Char)
    (comps: List (Pair Char (List Char))) (lastUpper: Bool)
    (word: others.all isWordChar = True)
    (starts: isWordStart first = True)
    (ends: rest.takeWhile isWordChar = [])
    (noDot: rest.head ≠ Some '.')
    (tail: QualTail first.isAsciiUppercase comps)
    (found: qualFound None comps = Some lastUpper):
    Parse.RunsFrom state (() => [Syntax.word False]) ([first, ..others] ++ qualChars comps) rest [
      {
        value = TokenLexeme (if lastUpper then Upper else Lower),
        offset = state.at.offset,
        length = ([first, ..others] ++ qualChars comps).length
      }
    ] :=
  Parse.runsFromBindAt state
    (() => Syntax.word False)
    (x => [x])
    ([first, ..others] ++ qualChars comps)
    []
    ([first, ..others] ++ qualChars comps)
    rest
    {
      value = TokenLexeme (if lastUpper then Upper else Lower),
      offset = state.at.offset,
      length = ([first, ..others] ++ qualChars comps).length
    }
    [
      {
        value = TokenLexeme (if lastUpper then Upper else Lower),
        offset = state.at.offset,
        length = ([first, ..others] ++ qualChars comps).length
      }
    ]
    (List.appendNil ([first, ..others] ++ qualChars comps)).flipped
    (runsFromWordQualified state first others rest comps lastUpper word starts ends noDot tail found)
    (middle atRest honest offset =>
      Parse.runsPure
        [
          {
            value = TokenLexeme (if lastUpper then Upper else Lower),
            offset = state.at.offset,
            length = ([first, ..others] ++ qualChars comps).length
          }
        ]
        rest
        middle)

--| A qualified name: components after the first, which no word character or `.` follows.
--|
--| Proof idea: As `itemReadsWord`: `item` tries the other lexemes first, none of which starts with a word start, then
--| the word is read (`runsFromWordQualifiedList`).
theorem itemReadsQualified ∀ (first: Char) (others rest: List Char)
    (comps: List (Pair Char (List Char))) (lastUpper: Bool)
    (starts: isWordStart first = True)
    (word: others.all isWordChar = True)
    (ends: rest.takeWhile isWordChar = [])
    (noDot: rest.head ≠ Some '.')
    (tail: QualTail first.isAsciiUppercase comps)
    (found: qualFound None comps = Some lastUpper):
    ItemReads ([first, ..others] ++ qualChars comps) (TokenLexeme (if lastUpper then Upper else Lower)) rest :=
  match first, starts with
    | '\n' | '}' | '{' | ' ' | '\r' | '\t' | '-' | '"' | '\'' | '.', starts => (Bool.falseNotTrue starts).impossible
    | other, starts =>
      itemReadsVia
        ([other, ..others] ++ qualChars comps)
        rest
        (TokenLexeme (if lastUpper then Upper else Lower))
        (self source state =>
          starts2 honest =>
            rewrite starts then
              runsFromWordQualifiedList state other others rest comps lastUpper word starts ends noDot tail found
                  starts2 honest)

-- Exponents.

--| An exponent's text: `e` or `E`, perhaps a sign, and digits.
def ExponentAs (exponent: List Char): Prop :=
  (∃ (marker: Char) (digit: Char) (digits: List Char) => exponent = [marker, digit, ..digits]
    ∧ (marker == 'e' || marker == 'E') = True
    ∧ digit.isAsciiDigit = True
    ∧ digits.all Char.isAsciiDigit = True)
    ∨ (∃ (marker: Char) (sign: Char) (digit: Char) (digits: List Char) => exponent = [marker, sign, digit, ..digits]
      ∧ (marker == 'e' || marker == 'E') = True
      ∧ (sign == '+' || sign == '-') = True
      ∧ digit.isAsciiDigit = True
      ∧ digits.all Char.isAsciiDigit = True)

theorem exponentSkipPlain ∀ (marker digit: Char) (more: List Char)
    (isMarker: (marker == 'e' || marker == 'E') = True)
    (isDigit: digit.isAsciiDigit = True):
    exponentSkip [marker, digit, ..more] = Some 1 :=
  let notSign: (digit == '+' || digit == '-') = False := arithmetic [isDigit]
  match more with
    | [] => rewrite isMarker, isDigit
    | [next, ..later] => rewrite isMarker, isDigit, notSign

theorem exponentSkipSigned ∀ (marker sign digit: Char) (more: List Char)
    (isMarker: (marker == 'e' || marker == 'E') = True)
    (isSign: (sign == '+' || sign == '-') = True)
    (isDigit: digit.isAsciiDigit = True):
    exponentSkip [marker, sign, digit, ..more] = Some 2 :=
  rewrite isMarker, isSign, isDigit

--| An exponent, which no digit follows: `exponentPart` reads it and gives `True`.
--|
--| Proof idea: `exponentSkip` counts the `e` and the sign, `skip` reads them and `span` the digits.
theorem runsExponent ∀ (exponent rest: List Char)
    (shape: ExponentAs exponent)
    (ends: rest.takeWhile Char.isAsciiDigit = []):
    Parse.Runs (() => exponentPart()) exponent rest True :=
  match exponent, shape with
    | exponent, Inl
        (Witness marker (Witness digit (Witness digits (Both same (Both isMarker (Both isDigit isDigits)))))) =>
      rewrite same then
        state =>
          Parse.runsFromMark state exponentFrom [marker, digit, ..digits] rest True (starts honest =>
            rewrite starts, exponentSkipPlain marker digit (digits ++ rest) isMarker isDigit then
              (Parse.runsBind
                    (() => skip 1)
                    (skipped =>
                      let power := Parse.span Char.isAsciiDigit
                      True)
                    [marker]
                    [digit, ..digits]
                    [marker, digit, ..digits]
                    rest
                    ()
                    True
                    byComputing
                    (runsSkip 1 [marker] ([digit, ..digits] ++ rest) byComputing)
                    (Parse.runsBind
                      (() => Parse.span Char.isAsciiDigit)
                      (power => True)
                      [digit, ..digits]
                      []
                      [digit, ..digits]
                      rest
                      [digit, ..digits]
                      True
                      (List.appendNil [digit, ..digits]).flipped
                      (Parse.runsSpan Char.isAsciiDigit [digit, ..digits] rest (Bool.andIntro isDigit isDigits) ends)
                      (Parse.runsPure True rest))) state starts honest)
    | exponent, Inr
        (Witness marker
          (Witness sign
            (Witness digit (Witness digits (Both same (Both isMarker (Both isSign (Both isDigit isDigits)))))))) =>
      rewrite same then
        state =>
          Parse.runsFromMark state exponentFrom [marker, sign, digit, ..digits] rest True (starts honest =>
            rewrite starts, exponentSkipSigned marker sign digit (digits ++ rest) isMarker isSign isDigit then
              (Parse.runsBind
                    (() => skip 2)
                    (skipped =>
                      let power := Parse.span Char.isAsciiDigit
                      True)
                    [marker, sign]
                    [digit, ..digits]
                    [marker, sign, digit, ..digits]
                    rest
                    ()
                    True
                    byComputing
                    (runsSkip 2 [marker, sign] ([digit, ..digits] ++ rest) byComputing)
                    (Parse.runsBind
                      (() => Parse.span Char.isAsciiDigit)
                      (power => True)
                      [digit, ..digits]
                      []
                      [digit, ..digits]
                      rest
                      [digit, ..digits]
                      True
                      (List.appendNil [digit, ..digits]).flipped
                      (Parse.runsSpan Char.isAsciiDigit [digit, ..digits] rest (Bool.andIntro isDigit isDigits) ends)
                      (Parse.runsPure True rest))) state starts honest)

--| A fraction's text: a `.`, a digit and more digits.
def FractionAs (fraction: List Char): Prop :=
  ∃ (second: Char) (more: List Char) => fraction = ['.', second, ..more]
    ∧ second.isAsciiDigit = True
    ∧ more.all Char.isAsciiDigit = True

--| What follows a number's digits when an exponent does and no fraction: the exponent is read and gives `True`.
theorem runsTailExponent ∀ (exponent rest: List Char)
    (shape: ExponentAs exponent)
    (ends: rest.takeWhile Char.isAsciiDigit = []):
    Parse.Runs (() => numberTail False) exponent rest True :=
  let noDot: (exponent ++ rest).head ≠ Some '.' := match exponent, shape with
    | exponent, Inl (Witness marker (Witness digit (Witness digits (Both same (Both isMarker rest2))))) =>
      rewrite same then List.headNeOfBeqFalse marker ([digit, ..digits] ++ rest) '.' (arithmetic [isMarker])
    | exponent, Inr
        (Witness marker (Witness sign (Witness digit (Witness digits (Both same (Both isMarker rest2)))))) =>
      rewrite same then List.headNeOfBeqFalse marker ([sign, digit, ..digits] ++ rest) '.' (arithmetic [isMarker])
  Parse.runsBind
    (() => fractionPart())
    (fraction =>
      let exponent2 := exponentPart()
      fraction || exponent2)
    []
    exponent
    exponent
    rest
    False
    True
    byComputing
    (runsFractionNone (exponent ++ rest) noDot)
    (Parse.runsBind
      (() => exponentPart())
      (exponent2 => False || exponent2)
      exponent
      []
      exponent
      rest
      True
      True
      (List.appendNil exponent).flipped
      (runsExponent exponent rest shape ends)
      (Parse.runsPure True rest))

--| What follows a number's digits when a fraction does and then an exponent.
theorem runsTailFractionExponent ∀ (fraction exponent rest: List Char)
    (fractionShape: FractionAs fraction)
    (exponentShape: ExponentAs exponent)
    (ends: rest.takeWhile Char.isAsciiDigit = []):
    Parse.Runs (() => numberTail False) (fraction ++ exponent) rest True :=
  let stops: (exponent ++ rest).takeWhile Char.isAsciiDigit = [] := match exponent, exponentShape with
    | _, Inl (Witness marker (Witness _ (Witness _ (Both same (Both isMarker _))))) |
        Inr (Witness marker (Witness _ (Witness _ (Witness _ (Both same (Both isMarker _)))))) =>
      rewrite same then (rewrite (arithmetic [isMarker]: marker.isAsciiDigit = False))
  match fraction, fractionShape with
    | fraction, Witness second (Witness more (Both same (Both digit digits))) =>
      rewrite same then
        Parse.runsBind
          (() => fractionPart())
          (fraction2 =>
            let exponent2 := exponentPart()
            fraction2 || exponent2)
          ['.', second, ..more]
          exponent
          (['.', second, ..more] ++ exponent)
          rest
          True
          True
          byComputing
          (runsFraction second more (exponent ++ rest) digit digits stops)
          (Parse.runsBind
            (() => exponentPart())
            (exponent2 => True || exponent2)
            exponent
            []
            exponent
            rest
            True
            True
            (List.appendNil exponent).flipped
            (runsExponent exponent rest exponentShape ends)
            (Parse.runsPure True rest))

-- Numbers.

theorem digitNotWordStart ∀ (char: Char) (digit: char.isAsciiDigit = True): isWordStart char = False :=
  let letter: char.isAsciiLetter = False := arithmetic [digit]
  let underscore: (char == '_') = False := arithmetic [digit]
  rewrite letter, underscore

theorem fractionNone ∀ (rest: List Char) (noDot: rest.head ≠ Some '.'): fractionAhead rest = False :=
  match rest, noDot with
    | [], noDot => byComputing
    | [next, ..more], noDot =>
      match next with
        | '.' => (noDot byComputing).impossible
        | other => byComputing

theorem exponentNone ∀ (rest: List Char) (noE: rest.head ≠ Some 'e' ∧ rest.head ≠ Some 'E'): exponentSkip rest = None :=
  match rest, noE with
    | [], noE => byComputing
    | [next, ..more], Both lower upper =>
      let notLower := List.beqFalseOfHeadNe next more 'e' lower
      let notUpper := List.beqFalseOfHeadNe next more 'E' upper
      match more with
        | [] => byComputing
        | [second, ..later] =>
          match later with
            | [] => rewrite notLower, notUpper
            | [third, ..others] => rewrite notLower, notUpper

theorem runsFractionNone ∀ (rest: List Char)
    (noDot: rest.head ≠ Some '.'):
    Parse.Runs (() => fractionPart()) [] rest False :=
  state =>
    Parse.runsFromMark state fractionFrom [] rest False (starts honest =>
      rewrite starts, fractionNone rest noDot then Parse.runsPure False rest state starts honest)

theorem runsExponentNone ∀ (rest: List Char)
    (noE: rest.head ≠ Some 'e' ∧ rest.head ≠ Some 'E'):
    Parse.Runs (() => exponentPart()) [] rest False :=
  state =>
    Parse.runsFromMark state exponentFrom [] rest False (starts honest =>
      rewrite starts, exponentNone rest noE then Parse.runsPure False rest state starts honest)

--| A fraction: a `.` and the digits after it, which no digit follows.
--|
--| Proof idea: `fractionAhead` holds, `skip 1` reads the `.` and `span` the digits.
theorem runsFraction ∀ (first: Char) (others rest: List Char)
    (digit: first.isAsciiDigit = True)
    (digits: others.all Char.isAsciiDigit = True)
    (ends: rest.takeWhile Char.isAsciiDigit = []):
    Parse.Runs (() => fractionPart()) ['.', first, ..others] rest True :=
  state =>
    Parse.runsFromMark state fractionFrom ['.', first, ..others] rest True (starts honest =>
      rewrite starts, digit then
        Parse.runsBind
          (() => skip 1)
          (skipped =>
            let decimals := Parse.span Char.isAsciiDigit
            True)
          ['.']
          [first, ..others]
          ['.', first, ..others]
          rest
          ()
          True
          byComputing
          (runsSkip 1 ['.'] ([first, ..others] ++ rest) byComputing)
          (Parse.runsBind
            (() => Parse.span Char.isAsciiDigit)
            (decimals => True)
            [first, ..others]
            []
            [first, ..others]
            rest
            [first, ..others]
            True
            (List.appendNil [first, ..others]).flipped
            (Parse.runsSpan Char.isAsciiDigit [first, ..others] rest (Bool.andIntro digit digits) ends)
            (Parse.runsPure True rest))
          state
          starts
          honest)

--| What follows a number's digits when nothing does that belongs to the number.
--|
--| Proof idea: Neither the fraction nor the exponent is there (`fractionNone`, `exponentNone`), so each reads nothing and gives `False`.
theorem runsTailNone ∀ (rest: List Char)
    (noDot: rest.head ≠ Some '.')
    (noE: rest.head ≠ Some 'e' ∧ rest.head ≠ Some 'E'):
    Parse.Runs (() => numberTail False) [] rest False :=
  Parse.runsBind
    (() => fractionPart())
    (fraction =>
      let exponent := exponentPart()
      fraction || exponent)
    []
    []
    []
    rest
    False
    False
    byComputing
    (runsFractionNone rest noDot)
    (Parse.runsBind
      (() => exponentPart())
      (exponent => False || exponent)
      []
      []
      []
      rest
      False
      False
      byComputing
      (runsExponentNone rest noE)
      (Parse.runsPure False rest))

--| What follows a number's digits when a fraction does and then nothing.
--|
--| Proof idea: The fraction reads (`runsFraction`) and gives `True`; the exponent isn't there.
theorem runsTailFraction ∀ (first: Char) (others rest: List Char)
    (digit: first.isAsciiDigit = True)
    (digits: others.all Char.isAsciiDigit = True)
    (ends: rest.takeWhile Char.isAsciiDigit = [])
    (noE: rest.head ≠ Some 'e' ∧ rest.head ≠ Some 'E'):
    Parse.Runs (() => numberTail False) ['.', first, ..others] rest True :=
  Parse.runsBind
    (() => fractionPart())
    (fraction =>
      let exponent := exponentPart()
      fraction || exponent)
    ['.', first, ..others]
    []
    ['.', first, ..others]
    rest
    True
    True
    (List.appendNil ['.', first, ..others]).flipped
    (runsFraction first others rest digit digits ends)
    (Parse.runsBind
      (() => exponentPart())
      (exponent => True || exponent)
      []
      []
      []
      rest
      False
      True
      byComputing
      (runsExponentNone rest noE)
      (Parse.runsPure True rest))

--| `number`: digits, then what `numberTail` read, with the kind that says.
--|
--| Proof idea: `span` of digits (`runsSpan`), then the tail, then `located` with `Float` if the tail was a fraction or exponent and `Num` if not.
theorem runsFromNumber ∀ (state: Parse.State Char) (digits tail read rest: List Char) (float: Bool)
    (joined: read = digits ++ tail)
    (all: digits.all Char.isAsciiDigit = True)
    (ends: (tail ++ rest).takeWhile Char.isAsciiDigit = [])
    (runsTail: Parse.Runs (() => numberTail False) tail rest float):
    Parse.RunsFrom state (() => number False) read rest {
      value = TokenLexeme (if float then Float else Num),
      offset = state.at.offset,
      length = read.length
    } :=
  Parse.runsFromMark state
    (numberFrom False)
    read
    rest
    { value = TokenLexeme (if float then Float else Num), offset = state.at.offset, length = read.length }
    (Parse.runsFromBind state
      (() => Parse.span Char.isAsciiDigit)
      (found =>
        let float2 := numberTail False
        located (TokenLexeme (if float2 then Float else Num)) state.at)
      digits
      tail
      read
      rest
      digits
      { value = TokenLexeme (if float then Float else Num), offset = state.at.offset, length = read.length }
      joined
      (Parse.runsSpan Char.isAsciiDigit digits (tail ++ rest) all ends)
      (middle atRest honest offset =>
        Parse.runsFromBind middle
          (() => numberTail False)
          (float2 => located (TokenLexeme (if float2 then Float else Num)) state.at)
          tail
          []
          tail
          rest
          float
          { value = TokenLexeme (if float then Float else Num), offset = state.at.offset, length = read.length }
          (List.appendNil tail).flipped
          runsTail
          (middle2 atRest2 honest2 offset2 =>
            runsFromLocatedAfter state middle2
              (TokenLexeme (if float then Float else Num))
              read
              rest
              atRest2
              honest2
              (arithmetic [offset, offset2, Eq.cong List.length joined, List.lengthAppend digits tail]))))

--| Digits and nothing that goes on with a number after them.
--|
--| Proof idea: `item` tries the other lexemes first, each on a first character that a digit isn't (ten literal cases) and a word start (`digitNotWordStart`); then `number` is read (`runsFromNumber`, with a tail that reads nothing).
theorem itemReadsNum ∀ (first: Char) (others rest: List Char)
    (digit: first.isAsciiDigit = True)
    (digits: others.all Char.isAsciiDigit = True)
    (ends: rest.takeWhile Char.isAsciiDigit = [])
    (noDot: rest.head ≠ Some '.')
    (noE: rest.head ≠ Some 'e' ∧ rest.head ≠ Some 'E'):
    ItemReads [first, ..others] (TokenLexeme Num) rest :=
  match first, digit with
    | '\n' | '}' | '{' | ' ' | '\r' | '\t' | '-' | '"' | '\'' | '.', digit => (Bool.falseNotTrue digit).impossible
    | other, digit => itemReadsVia [other, ..others] rest (TokenLexeme Num) (self source state =>
      starts honest =>
        let all: [other, ..others].all Char.isAsciiDigit = True := Bool.andIntro digit digits
        let ran :=
          runsFromNumber state
            [other, ..others]
            []
            [other, ..others]
            rest
            False
            (List.appendNil [other, ..others]).flipped
            all
            ends
            (runsTailNone rest noDot noE)
        rewrite digitNotWordStart other digit, digit then
          (Parse.runsFromBindAt state
            (() => number False)
            (x => [x])
            [other, ..others]
            []
            [other, ..others]
            rest
            { value = TokenLexeme Num, offset = state.at.offset, length = [other, ..others].length }
            [{ value = TokenLexeme Num, offset = state.at.offset, length = [other, ..others].length }]
            (List.appendNil [other, ..others]).flipped
            ran
            (middle atRest2 honest2 offset2 =>
              Parse.runsPure
                [{ value = TokenLexeme Num, offset = state.at.offset, length = [other, ..others].length }]
                rest
                middle)
            starts
            honest))

--| What follows a float's digits: a fraction, an exponent, or both.
def FloatTailAs (tail: List Char): Prop :=
  (∃ (fraction: List Char) (exponent: List Char) => tail = fraction ++ exponent
    ∧ FractionAs fraction
    ∧ ExponentAs exponent)
    ∨ FractionAs tail
    ∨ ExponentAs tail

theorem fractionStops ∀ (fraction rest: List Char)
    (shape: FractionAs fraction):
    (fraction ++ rest).takeWhile Char.isAsciiDigit = [] :=
  match fraction, shape with | fraction, Witness second (Witness more (Both same rest2)) => rewrite same

theorem exponentStops ∀ (exponent rest: List Char)
    (shape: ExponentAs exponent):
    (exponent ++ rest).takeWhile Char.isAsciiDigit = [] :=
  match exponent, shape with
    | _, Inl (Witness marker (Witness _ (Witness _ (Both same (Both isMarker _))))) |
        Inr (Witness marker (Witness _ (Witness _ (Witness _ (Both same (Both isMarker _)))))) =>
      rewrite same then (rewrite (arithmetic [isMarker]: marker.isAsciiDigit = False))

--| A float's tail doesn't start with a digit.
theorem floatTailStops ∀ (tail rest: List Char)
    (shape: FloatTailAs tail):
    (tail ++ rest).takeWhile Char.isAsciiDigit = [] :=
  match shape with
    | Inl (Witness fraction (Witness exponent (Both same (Both fs es)))) =>
      rewrite same then
        match fraction, fs with
          | fraction, Witness second (Witness more (Both same2 rest2)) => rewrite same2
    | Inr (Inl fs) => fractionStops tail rest fs
    | Inr (Inr es) => exponentStops tail rest es

--| What follows a float's digits is read by `numberTail`, which gives `True`.
theorem runsTailFloat ∀ (tail rest: List Char)
    (shape: FloatTailAs tail)
    (ends: rest.takeWhile Char.isAsciiDigit = [])
    (noE: rest.head ≠ Some 'e' ∧ rest.head ≠ Some 'E'):
    Parse.Runs (() => numberTail False) tail rest True :=
  match shape with
    | Inl (Witness fraction (Witness exponent (Both same (Both fs es)))) =>
      rewrite same then runsTailFractionExponent fraction exponent rest fs es ends
    | Inr (Inl (Witness second (Witness more (Both same (Both decimal decimals))))) =>
      rewrite same then runsTailFraction second more rest decimal decimals ends noE
    | Inr (Inr es) => runsTailExponent tail rest es ends

--| A float: digits and a tail that is a fraction, an exponent or both, with nothing after it that goes on with the
--| number.
--|
--| Proof idea: As `itemReadsNum`, with the tail read by `runsTailFloat`.
theorem itemReadsFloatTail ∀ (first: Char) (others tail rest read: List Char)
    (split: read = [first, ..others] ++ tail)
    (digit: first.isAsciiDigit = True)
    (digits: others.all Char.isAsciiDigit = True)
    (shape: FloatTailAs tail)
    (ends: rest.takeWhile Char.isAsciiDigit = [])
    (noE: rest.head ≠ Some 'e' ∧ rest.head ≠ Some 'E'):
    ItemReads read (TokenLexeme Float) rest :=
  rewrite split then
    match first, digit with
      | '\n' | '}' | '{' | ' ' | '\r' | '\t' | '-' | '"' | '\'' | '.', digit => (Bool.falseNotTrue digit).impossible
      | other, digit => itemReadsVia ([other, ..others] ++ tail) rest (TokenLexeme Float) (self source state =>
        starts honest =>
          let all: [other, ..others].all Char.isAsciiDigit = True := Bool.andIntro digit digits
          rewrite digitNotWordStart other digit, digit then
            Parse.runsFromBindAt state
              (() => number False)
              (x => [x])
              ([other, ..others] ++ tail)
              []
              ([other, ..others] ++ tail)
              rest
              { value = TokenLexeme Float, offset = state.at.offset, length = ([other, ..others] ++ tail).length }
              [{ value = TokenLexeme Float, offset = state.at.offset, length = ([other, ..others] ++ tail).length }]
              (List.appendNil ([other, ..others] ++ tail)).flipped
              (runsFromNumber state
                [other, ..others]
                tail
                ([other, ..others] ++ tail)
                rest
                True
                byComputing
                all
                (floatTailStops tail rest shape)
                (runsTailFloat tail rest shape ends noE))
              (middle atRest2 honest2 offset2 =>
                Parse.runsPure
                  [{ value = TokenLexeme Float, offset = state.at.offset, length = ([other, ..others] ++ tail).length }]
                  rest
                  middle)
              starts
              honest)

-- The interface the printer's proofs use: a token's spelling, what may follow it, and that it reads as that token.

--| What the lexer reads a name as: with no components after the first it is `wordKind`'s, with some it is the last
--| component's case.
def NameKind (kind: Tok) (text: Text): List (Pair Char (List Char)) → Prop
  | [] => wordKind False text = kind
  | [component, ..more] =>
    ∃ (lastUpper: Bool) => qualFound None [component, ..more] = Some lastUpper
      ∧ (if lastUpper then Upper else Lower) = kind

--| The texts that are a token of this kind (as the lexer spells it, `crates/syntax`'s lexer), for the slice 1
--| alphabet: fixed spellings, with the Unicode one for seven, names, and numbers.
def Spells: Tok → Text → Prop
  | LParen, text => text = "("
  | RParen, text => text = ")"
  | LBracket, text => text = "["
  | RBracket, text => text = "]"
  | Comma, text => text = ","
  | Colon, text => text = ":"
  | ColonEq, text => text = ":="
  | Equals, text => text = "="
  | EqEq, text => text = "=="
  | Arrow, text => text = "->" ∨ text = "→"
  | OrOr, text => text = "||" ∨ text = "∨"
  | AndAnd, text => text = "&&" ∨ text = "∧"
  | Plus, text => text = "+"
  | PlusPlus, text => text = "++"
  | Minus, text => text = "-"
  | Star, text => text = "*"
  | Slash, text => text = "/"
  | Percent, text => text = "%"
  | NotEq, text => text = "!=" ∨ text = "≠"
  | Lt, text => text = "<"
  | Le, text => text = "<=" ∨ text = "≤"
  | Gt, text => text = ">"
  | Ge, text => text = ">=" ∨ text = "≥"
  | Bang, text => text = "!" ∨ text = "¬"
  | KwDef, text => text = "def"
  | Lower, text =>
    ∃ (first: Char) (others: List Char) (comps: List (Pair Char (List Char))) => text.toList
      = [first, ..others] ++ qualChars comps
      ∧ isWordStart first = True
      ∧ others.all isWordChar = True
      ∧ QualTail first.isAsciiUppercase comps
      ∧ NameKind Lower text comps
  | Upper, text =>
    ∃ (first: Char) (others: List Char) (comps: List (Pair Char (List Char))) => text.toList
      = [first, ..others] ++ qualChars comps
      ∧ isWordStart first = True
      ∧ others.all isWordChar = True
      ∧ QualTail first.isAsciiUppercase comps
      ∧ NameKind Upper text comps
  | Num, text =>
    ∃ (first: Char) (others: List Char) => text.toList = [first, ..others]
      ∧ first.isAsciiDigit = True
      ∧ others.all Char.isAsciiDigit = True
  | Float, text =>
    ∃ (first: Char) (others: List Char) (tail: List Char) => text.toList = [first, ..others] ++ tail
      ∧ first.isAsciiDigit = True
      ∧ others.all Char.isAsciiDigit = True
      ∧ FloatTailAs tail
  | _, text => False

--| What the text after a token may start with, so that the lexer reads the token and no more: not a character that
--| goes on a name or a number, nor one that makes a longer operator (`:` and `=`, `<` and `-`), nor a `.`.
def MayFollow (kind: Tok) (text: Text) (rest: List Char): Prop := match kind with
  | Colon => rest.head ≠ Some '='
  | Equals => rest.head ≠ Some '=' ∧ rest.head ≠ Some '>'
  | Plus => rest.head ≠ Some '+'
  | Minus => rest.head ≠ Some '-' ∧ rest.head ≠ Some '>'
  | Lt => rest.head ≠ Some '=' ∧ rest.head ≠ Some '-'
  | Gt => rest.head ≠ Some '='
  | Bang => text = "!" → rest.head ≠ Some '=' ∧ rest.takeWhile isWordChar ≠ ['i', 'n']
  | KwDef | Lower | Upper => rest.takeWhile isWordChar = [] ∧ rest.head ≠ Some '.'
  | Num => rest.takeWhile Char.isAsciiDigit = [] ∧ rest.head ≠ Some '.' ∧ (rest.head ≠ Some 'e' ∧ rest.head ≠ Some 'E')
  | Float => rest.takeWhile Char.isAsciiDigit = [] ∧ (rest.head ≠ Some 'e' ∧ rest.head ≠ Some 'E')
  | _ => True

--| A name, plain or qualified, that nothing goes on with: one `item` read as the kind `NameKind` says.
theorem itemReadsName ∀ (kind: Tok) (text: Text) (first: Char) (others: List Char)
    (comps: List (Pair Char (List Char))) (rest: List Char)
    (split: text.toList = [first, ..others] ++ qualChars comps)
    (starts: isWordStart first = True)
    (word: others.all isWordChar = True)
    (tail: QualTail first.isAsciiUppercase comps)
    (kinded: NameKind kind text comps)
    (ends: rest.takeWhile isWordChar = [])
    (noDot: rest.head ≠ Some '.'):
    ItemReads text.toList (TokenLexeme kind) rest :=
  match comps, split, tail, kinded with
    | [], split, tail, kinded =>
      let plain: text.toList = [first, ..others] := Eq.trans split (List.appendNil [first, ..others])
      rewrite plain then
        itemReadsWord first others rest kind starts word ends noDot (rewrite <- plain, Text.fromToList text then kinded)
    | [component, ..more], split, tail, Witness lastUpper (Both found isKind) =>
      let ran := itemReadsQualified first others rest [component, ..more] lastUpper starts word ends noDot tail found
      rewrite split then (rewrite isKind at ran then ran)

--| `lexWord1`: a text that spells a token of slice 1's alphabet, followed by something it may be followed by, is read
--| by the lexer's `item` as that token, whatever follows after that.
--|
--| Proof idea: one case per kind and spelling, each the per-token theorem (`itemReadsColon`, `itemReadsWord`, …)
--| with the text's spelling rewritten in and `MayFollow`'s conditions handed on.
theorem lexWord1 ∀ (kind: Tok) (text: Text) (rest: List Char)
    (spells: Spells kind text)
    (follows: MayFollow kind text rest):
    ItemReads text.toList (TokenLexeme kind) rest :=
  match kind, spells, follows with
    | LParen, same, follows => rewrite same then itemReadsLParen rest
    | RParen, same, follows => rewrite same then itemReadsRParen rest
    | LBracket, same, follows => rewrite same then itemReadsLBracket rest
    | RBracket, same, follows => rewrite same then itemReadsRBracket rest
    | Comma, same, follows => rewrite same then itemReadsComma rest
    | Colon, same, follows => rewrite same then itemReadsColon rest follows
    | ColonEq, same, follows => rewrite same then itemReadsColonEq rest
    | Equals, same, follows => rewrite same then itemReadsEquals rest follows
    | EqEq, same, follows => rewrite same then itemReadsEqEq rest
    | Arrow, Inl same, follows => rewrite same then itemReadsArrow rest
    | Arrow, Inr same, follows => rewrite same then itemReadsArrowUnicode rest
    | OrOr, Inl same, follows => rewrite same then itemReadsOrOr rest
    | OrOr, Inr same, follows => rewrite same then itemReadsOrOrUnicode rest
    | AndAnd, Inl same, follows => rewrite same then itemReadsAndAnd rest
    | AndAnd, Inr same, follows => rewrite same then itemReadsAndAndUnicode rest
    | Plus, same, follows => rewrite same then itemReadsPlus rest follows
    | PlusPlus, same, follows => rewrite same then itemReadsPlusPlus rest
    | Minus, same, follows => rewrite same then itemReadsMinus rest follows
    | Star, same, follows => rewrite same then itemReadsStar rest
    | Slash, same, follows => rewrite same then itemReadsSlash rest
    | Percent, same, follows => rewrite same then itemReadsPercent rest
    | NotEq, Inl same, follows => rewrite same then itemReadsNotEq rest
    | NotEq, Inr same, follows => rewrite same then itemReadsNotEqUnicode rest
    | Lt, same, follows => rewrite same then itemReadsLt rest follows
    | Le, Inl same, follows => rewrite same then itemReadsLe rest
    | Le, Inr same, follows => rewrite same then itemReadsLeUnicode rest
    | Gt, same, follows => rewrite same then itemReadsGt rest follows
    | Ge, Inl same, follows => rewrite same then itemReadsGe rest
    | Ge, Inr same, follows => rewrite same then itemReadsGeUnicode rest
    | Bang, Inl same, follows => rewrite same then (itemReadsBang rest (follows same))
    | Bang, Inr same, follows => rewrite same then itemReadsBangUnicode rest
    | KwDef, same, Both ends noDot =>
      rewrite same then itemReadsWord 'd' ['e', 'f'] rest KwDef byComputing byComputing ends noDot byComputing
    | Lower, Witness first
        (Witness others (Witness comps (Both split (Both starts (Both word (Both tail kinded)))))), Both ends noDot =>
      itemReadsName Lower text first others comps rest split starts word tail kinded ends noDot
    | Upper, Witness first
        (Witness others (Witness comps (Both split (Both starts (Both word (Both tail kinded)))))), Both ends noDot =>
      itemReadsName Upper text first others comps rest split starts word tail kinded ends noDot
    | Num, Witness first (Witness others (Both split (Both digit digits))), Both ends (Both noDot noE) =>
      rewrite split then itemReadsNum first others rest digit digits ends noDot noE
    | Float, Witness first (Witness others (Witness tail (Both split (Both digit (Both digits shape))))), Both ends
          noE => itemReadsFloatTail first others tail rest text.toList split digit digits shape ends noE

-- Pieces that lex.

--| A piece is spelled so that the lexer reads it as the lexeme it stands for: a token as `Spells` says, a comment as
--| `--` and a line, spaces and a break as they are.
def Piece.Spells: Piece → Prop
  | Code kind text => Syntax.Proofs.Spells kind text
  | Gap _ | Break => True
  | Remark text =>
    ∃ (others: List Char) => text.toList = ['-', '-', ..others] ∧ others.all (char => char != '\n') = True

--| What the text after a piece may start with: the token's `MayFollow`, no more spaces after spaces, a comment
--| ends the line.
def Piece.Follows (piece: Piece) (rest: List Char): Prop := match piece with
  | Code kind text => MayFollow kind text rest
  | Gap count => rest.head ≠ Some ' ' ∧ rest.head ≠ Some '\r'
  | Break => True
  | Remark text => rest.takeWhile (char => char != '\n') = []

--| Each piece is spelled as the lexer reads it and what follows it may follow it.
def Lexable: (pieces: List Piece) → (rest: List Char) → Prop
  | [], rest => True
  | [piece, ..more], rest =>
    piece.Spells ∧ piece.Follows (Parse.joinReads (pieceSteps more) ++ rest) ∧ Lexable more rest

theorem pieceReads ∀ (piece: Piece) (rest: List Char) (plain: piece.Plain)
    (spells: piece.Spells) (follows: piece.Follows rest):
    ItemReads piece.chars piece.lexeme rest :=
  match piece, plain, spells, follows with
    | Code kind text, Both nonEmpty noBreak, spells, follows => lexWord1 kind text rest spells follows
    | Gap count, positive, spells, follows => itemReadsSpaces count rest positive follows
    | Break, plain, spells, follows => itemReadsBreak rest
    | Remark text, Both nonEmpty noBreak, Witness others (Both split oneLine), follows =>
      rewrite split then itemReadsComment others rest oneLine follows

theorem nonEmptyChars ∀ (piece: Piece) (plain: piece.Plain): piece.chars ≠ [] := match piece, plain with
  | Code kind text, Both nonEmpty noBreak => nonEmpty
  | Gap count, positive =>
    match count, positive with
      | Zero, positive => (positive byComputing).impossible
      | Succ more, positive => same => cases
  | Break, plain => same => cases
  | Remark text, Both nonEmpty noBreak => nonEmpty

theorem lexableRounds ∀ (self: Place → {Parse Char} List (Parse.Located Lexeme)) (source: Text)
    (pieces: List Piece) (rest: List Char)
    (plain: AllPlain pieces)
    (lexable: Lexable pieces rest)
    (ends: rest = []):
    ItemRounds self source (pieceSteps pieces) rest :=
  match pieces, plain, lexable with
    | [], plain, lexable => rewrite ends then declinesItemEnd self source
    | [piece, ..more], Both pieceOk moreOk, Both spells (Both follows later) => (
      nonEmptyChars piece pieceOk,
      pieceReads piece (Parse.joinReads (pieceSteps more) ++ rest) pieceOk spells follows,
      lexableRounds self source more rest moreOk later ends
    )

--| The text of pieces, as the printer writes it.
def piecesText (pieces: List Piece): Text := Text.fromList (Parse.joinReads (pieceSteps pieces))

--| `lexPrinted`, from what the pieces are: spelled as the lexer reads them, with nothing after the last, lex to the
--| leaves of their layout.
--|
--| Proof idea: `lexableRounds` makes each piece's `ItemReads` from `pieceReads`, and `declinesItemEnd` ends the rounds.
theorem lexPieces ∀ (pieces: List Piece)
    (plain: AllPlain pieces)
    (lexable: Lexable pieces []):
    lex (piecesText pieces)
      = Ok {
        leaves = (pieces.foldLeft Laid.start Laid.lay).leaves.reverse,
        end = {
          leading = (pieces.foldLeft Laid.start Laid.lay).pending.reverse,
          blankLines = (pieces.foldLeft Laid.start Laid.lay).blankRun,
          trailing = None
        }
      } :=
  lexPrinted
    (piecesText pieces)
    pieces
    (Text.toFromList (Parse.joinReads (pieceSteps pieces)))
    (self => lexableRounds self (piecesText pieces) pieces [] plain lexable byComputing)
    plain

theorem wordCharNoBreak ∀ (char: Char) (word: isWordChar char = True): ((char != '\n'): Bool) = True :=
  arithmetic [word]

theorem digitNoBreak ∀ (char: Char) (digit: char.isAsciiDigit = True): ((char != '\n'): Bool) = True :=
  arithmetic [digit]

theorem qualCharsNoBreak ∀ (upper: Bool) (comps: List (Pair Char (List Char)))
    (tail: QualTail upper comps):
    (qualChars comps).all (char => char != '\n') = True :=
  match comps, tail with
    | [], tail => byComputing
    | [(letter, word), ..more], Both isUpper (Both isLetter (Both isWord next)) =>
      Bool.andIntro byComputing
        (Bool.andIntro
          (wordCharNoBreak letter (letterWordChar letter isLetter))
          (List.allAppendTrue word
            (qualChars more)
            (char => char != '\n')
            (List.allImpliesBool word isWordChar (char => char != '\n') wordCharNoBreak isWord)
            (qualCharsNoBreak letter.isAsciiUppercase more next)))

theorem exponentNoBreak ∀ (exponent: List Char)
    (shape: ExponentAs exponent):
    exponent.all (char => char != '\n') = True :=
  match exponent, shape with
    | exponent, Inl
        (Witness marker (Witness digit (Witness digits (Both same (Both isMarker (Both isDigit isDigits)))))) =>
      rewrite same then
        Bool.andIntro
          (arithmetic [isMarker])
          (Bool.andIntro
            (digitNoBreak digit isDigit)
            (List.allImpliesBool digits Char.isAsciiDigit (char => char != '\n') digitNoBreak isDigits))
    | exponent, Inr
        (Witness marker
          (Witness sign
            (Witness digit (Witness digits (Both same (Both isMarker (Both isSign (Both isDigit isDigits)))))))) =>
      rewrite same then
        Bool.andIntro
          (arithmetic [isMarker])
          (Bool.andIntro
            (arithmetic [isSign])
            (Bool.andIntro
              (digitNoBreak digit isDigit)
              (List.allImpliesBool digits Char.isAsciiDigit (char => char != '\n') digitNoBreak isDigits)))

theorem fractionNoBreak ∀ (fraction: List Char)
    (shape: FractionAs fraction):
    fraction.all (char => char != '\n') = True :=
  match fraction, shape with
    | fraction, Witness second (Witness more (Both same (Both digit digits))) =>
      rewrite same then
        Bool.andIntro byComputing
          (Bool.andIntro
            (digitNoBreak second digit)
            (List.allImpliesBool more Char.isAsciiDigit (char => char != '\n') digitNoBreak digits))

theorem floatTailNoBreak ∀ (tail: List Char) (shape: FloatTailAs tail): tail.all (char => char != '\n') = True :=
  match shape with
    | Inl (Witness fraction (Witness exponent (Both same (Both fs es)))) =>
      rewrite same then
        List.allAppendTrue fraction exponent
          (char => char != '\n')
          (fractionNoBreak fraction fs)
          (exponentNoBreak exponent es)
    | Inr (Inl fs) => fractionNoBreak tail fs
    | Inr (Inr es) => exponentNoBreak tail es

--| A spelled token has something in it and no line break.
--|
--| Proof idea: Each fixed spelling is a literal; names and numbers are made of characters that aren't a line break (`wordCharNoBreak`, `digitNoBreak`).
theorem spellsPlain ∀ (kind: Tok) (text: Text) (spells: Spells kind text): (Code kind text).Plain :=
  match kind, spells with
    | LParen | RParen | LBracket | RBracket | Comma | Colon | ColonEq | Equals | EqEq, same =>
      rewrite same then Both byDecision byComputing
    | Arrow | OrOr | AndAnd, Inl same | Inr same => rewrite same then Both byDecision byComputing
    | Plus | PlusPlus | Minus | Star | Slash | Percent, same => rewrite same then Both byDecision byComputing
    | NotEq, Inl same | Inr same => rewrite same then Both byDecision byComputing
    | Lt, same => rewrite same then Both byDecision byComputing
    | Le, Inl same | Inr same => rewrite same then Both byDecision byComputing
    | Gt, same => rewrite same then Both byDecision byComputing
    | Ge | Bang, Inl same | Inr same => rewrite same then Both byDecision byComputing
    | KwDef, same => rewrite same then Both byDecision byComputing
    | Lower | Upper, Witness first
        (Witness others (Witness comps (Both split (Both starts (Both word (Both tail _)))))) =>
      Both
        (rewrite split then different => cases)
        (rewrite split then
          Bool.andIntro
            (wordCharNoBreak first (wordStartChar first starts))
            (List.allAppendTrue others
              (qualChars comps)
              (char => char != '\n')
              (List.allImpliesBool others isWordChar (char => char != '\n') wordCharNoBreak word)
              (qualCharsNoBreak first.isAsciiUppercase comps tail)))
    | Num, Witness first (Witness others (Both split (Both digit digits))) =>
      Both
        (rewrite split then different => cases)
        (rewrite split then
          Bool.andIntro
            (digitNoBreak first digit)
            (List.allImpliesBool others Char.isAsciiDigit (char => char != '\n') digitNoBreak digits))
    | Float, Witness first (Witness others (Witness tail (Both split (Both digit (Both digits shape))))) =>
      Both
        (rewrite split then different => cases)
        (rewrite split then
          Bool.andIntro
            (digitNoBreak first digit)
            (List.allAppendTrue others tail
              (char => char != '\n')
              (List.allImpliesBool others Char.isAsciiDigit (char => char != '\n') digitNoBreak digits)
              (floatTailNoBreak tail shape)))

theorem piecesTextOne ∀ (kind: Tok) (text: Text): piecesText [Code kind text] = text :=
  rewrite List.appendNil text.toList then Text.fromToList text

--| A token alone: a text that spells it, with nothing after it that goes on with it, lexes to that one token at the
--| start of a line with no comments around it.
theorem lexesAsSpells ∀ (kind: Tok) (text: Text)
    (spells: Spells kind text)
    (follows: MayFollow kind text []):
    LexesAs text kind :=
  let ran :=
    lexPieces
      [Code kind text]
      (Both (spellsPlain kind text spells) byComputing)
      (Both spells (Both follows byComputing))
  rewrite piecesTextOne kind text at ran then ran

--| Nothing follows the last token of a text, so nothing keeps it from being read whole.
theorem mayFollowEnd ∀ (kind: Tok) (text: Text): MayFollow kind text [] := match kind with
  | Colon => byDecision
  | Equals => Both byDecision byDecision
  | Plus => byDecision
  | Minus | Lt => Both byDecision byDecision
  | Gt => byDecision
  | Bang => same => Both byDecision byDecision
  | KwDef | Lower | Upper => Both byComputing byDecision
  | Num => Both byComputing (Both byDecision (Both byDecision byDecision))
  | Float => Both byComputing (Both byDecision byDecision)
  | other => byComputing

-- The operator table against the lexer.

--| The kinds of slice 1's alphabet that are punctuation or operators: all but names, numbers and `def`.
def Tok.symbolic1: Tok → Bool
  | Lower | Upper | Num | Float | KwDef => False
  | kind => kind.within1

--| `operatorTok`, which the rules use to tell which operator a word is, gives the kind the lexer gives, for each
--| spelling of it.
--|
--| Proof idea: One literal case per kind and spelling, each by computing.
theorem operatorTokOfSpells ∀ (kind: Tok) (text: Text)
    (spells: Spells kind text)
    (symbolic: kind.symbolic1 = True):
    operatorTok text = Some kind :=
  match kind, spells, symbolic with
    | LParen | RParen | LBracket | RBracket | Comma | Colon | ColonEq | Equals | EqEq, same, _ => rewrite same
    | Arrow | OrOr | AndAnd, Inl same | Inr same, _ => rewrite same
    | Plus | PlusPlus | Minus | Star | Slash | Percent, same, _ => rewrite same
    | NotEq, Inl same | Inr same, _ => rewrite same
    | Lt, same, symbolic => rewrite same
    | Le, Inl same | Inr same, _ => rewrite same
    | Gt, same, symbolic => rewrite same
    | Ge | Bang, Inl same | Inr same, _ => rewrite same
    | other, spells, symbolic => (Bool.falseNotTrue symbolic).impossible

-- Pieces and the pieces next to them.

--| Two texts start alike for what may follow a token: the same first character, and the second starts with the
--| word `in` only if the first does (a `!` before `in` is read as `!in`).
def StartsAlike (before after: List Char): Prop :=
  before.head = after.head ∧ (after.takeWhile isWordChar = ['i', 'n'] → before.takeWhile isWordChar = ['i', 'n'])

theorem alikeSame ∀ (chars: List Char): StartsAlike chars chars := Both byComputing (run => run)

theorem alikeOfEq ∀ (before after: List Char) (same: before = after): StartsAlike before after :=
  rewrite same then alikeSame after

--| Texts with the same first character, a space, start alike.
theorem alikeOfSpace ∀ (before after: List Char)
    (same: before.head = after.head)
    (space: after.head = Some ' '):
    StartsAlike before after :=
  Both same (run =>
    let stops := List.takeWhileHeadFails isWordChar after ' ' space byComputing
    let never: [] = ['i', 'n'] := Eq.trans stops.flipped run
    cases)

--| Where the name characters at the start of `front ++ back` are `in`, those of `front` are, or `front` is `i` and
--| those of `back` are `n`.
--|
--| Proof idea: Cases on the first two characters of `front` and whether they are name characters.
theorem inOfAppend ∀ (front back: List Char)
    (filled: front ≠ [])
    (run: (front ++ back).takeWhile isWordChar = ['i', 'n']):
    front.takeWhile isWordChar = ['i', 'n'] ∨ (front = ['i'] ∧ back.takeWhile isWordChar = ['n']) :=
  match front with
    | [] => (filled byComputing).impossible
    | [first, ..more] =>
      match firstWord: isWordChar first with
        | True =>
          let isI: first = 'i' := List.consInjectiveHead run
          let tail: (more ++ back).takeWhile isWordChar = ['n'] :=
            List.consInjective first _ ['n'] (rewrite isI at run then rewrite isI then run)
          match more with
            | [] => Inr (Both (rewrite isI) tail)
            | [second, ..later] =>
              match secondWord: isWordChar second with
                | True =>
                  let isN: second = 'n' := List.consInjectiveHead tail
                  let rest: (later ++ back).takeWhile isWordChar = [] :=
                    List.consInjective second _ [] (rewrite isN at tail then rewrite isN then tail)
                  Inl (rewrite isI, isN, List.takeWhileNilPrefix isWordChar later back rest)

theorem notI ∀ (char: Char) (others: List Char) (differs: char ≠ 'i') (same: [char, ..others] = ['i']): Void :=
  differs (List.consInjectiveHead same)

theorem notJustI ∀ (piece: Piece) (rest: List Char) (spells: piece.Spells) (follows: piece.Follows rest)
    (single: piece.chars = ['i'])
    (run: rest.takeWhile isWordChar = ['n']):
    Void :=
  match piece, spells, follows with
    | Gap count, _, _ =>
      match count with
        | Zero => cases
        | Succ more => cases
    | Break, _, _ => cases
    | Remark text, Witness others (Both split _), _ =>
      let never: ['-', '-', ..others] = ['i'] := Eq.trans split.flipped single
      cases
    | Code LParen _ |
        Code RParen _ |
        Code LBracket _ |
        Code RBracket _ |
        Code Comma _ |
        Code Colon _ |
        Code ColonEq _ |
        Code Equals _ |
        Code EqEq _, same, _ => rewrite same at single then notI _ _ byDecision single
    | Code Arrow _ | Code OrOr _ | Code AndAnd _, Inl same | Inr same, _ =>
      rewrite same at single then notI _ _ byDecision single
    | Code Plus _ | Code PlusPlus _ | Code Minus _ | Code Star _ | Code Slash _ | Code Percent _, same, _ =>
      rewrite same at single then notI _ _ byDecision single
    | Code NotEq _, Inl same | Inr same, _ => rewrite same at single then notI _ _ byDecision single
    | Code Lt text, same, _ => rewrite same at single then notI _ _ byDecision single
    | Code Le _, Inl same | Inr same, _ => rewrite same at single then notI _ _ byDecision single
    | Code Gt text, same, _ => rewrite same at single then notI _ _ byDecision single
    | Code Ge _ | Code Bang _, Inl same | Inr same, _ => rewrite same at single then notI _ _ byDecision single
    | Code KwDef _ | Code Lower _ | Code Upper _, _, Both ends _ =>
      let never: [] = ['n'] := Eq.trans ends.flipped run
      cases
    | Code Num text, Witness first (Witness others (Both split (Both digit _))), _ =>
      let isI: first = 'i' := List.consInjectiveHead (Eq.trans split.flipped single)
      rewrite isI at digit then cases
    | Code Float text, Witness first (Witness others (Witness tail (Both split (Both digit _)))), _ =>
      let joined: [first, ..others ++ tail] = ['i'] := Eq.trans split.flipped single
      let isI: first = 'i' := List.consInjectiveHead joined
      rewrite isI at digit then cases

--| A piece's characters, and the same with what may follow the piece after them, start alike.
--|
--| Proof idea: The first character is the piece's. If the name characters at the start of the whole are `in`, they
--| are the piece's unless the piece is `i` and what follows starts `n`, which no piece allows (`notJustI`).
theorem alikeAppend ∀ (piece: Piece) (rest: List Char) (plain: piece.Plain)
    (spells: piece.Spells) (follows: piece.Follows rest):
    StartsAlike piece.chars (piece.chars ++ rest) :=
  let joined := List.headAppendMiddle piece.chars [] rest (nonEmptyChars piece plain)
  Both (rewrite List.appendNil piece.chars at joined then joined.flipped) (run =>
    match inOfAppend piece.chars rest (nonEmptyChars piece plain) run with
      | Inl front => front
      | Inr (Both single after) => (notJustI piece rest spells follows single after).impossible)

--| What a token needs of the text after it depends only on how that text starts (`StartsAlike`).
--|
--| Proof idea: Each condition of `MayFollow` is about the head or about `takeWhile` stopping at it (`List.takeWhileSameHead`);
--| a `!`'s is about the word `in`, which `StartsAlike` carries.
theorem followsAlike ∀ (piece: Piece) (before after: List Char)
    (alike: StartsAlike before after) (follows: piece.Follows before):
    piece.Follows after :=
  let same := alike.left
  match piece, follows with
    | Code Colon _ | Code Equals _ | Code Plus _ | Code Minus _ | Code Lt _ | Code Gt _, follows =>
      rewrite <- same then follows
    | Code Bang text, follows => bang =>
      match follows bang with
        | Both noEq notIn => Both (rewrite <- same then noEq) (word => notIn (alike.right word))
    | Code KwDef _ | Code Lower _ | Code Upper _, Both stops noDot =>
      Both (List.takeWhileSameHead isWordChar before after same stops) (rewrite <- same then noDot)
    | Code Num text, Both stops (Both noDot noE) =>
      Both (List.takeWhileSameHead Char.isAsciiDigit before after same stops) (rewrite <- same then Both noDot noE)
    | Code Float text, Both stops noE =>
      Both (List.takeWhileSameHead Char.isAsciiDigit before after same stops) (rewrite <- same then noE)
    | Code other text, follows => follows
    | Gap count, follows => rewrite <- same then follows
    | Break, follows => follows
    | Remark text, follows => List.takeWhileSameHead (char => char != '\n') before after same follows

--| Each piece of a list is spelled as the lexer reads it.
def AllSpelled: List Piece → Prop
  | [] => True
  | [piece, ..more] => piece.Spells ∧ AllSpelled more

--| What each piece needs of the one after it, and the last of the end of the text: the pairs of neighbours.
def PairsFollow: List Piece → Prop
  | [] => True
  | [piece] => piece.Follows []
  | [piece, next, ..more] => piece.Follows next.chars ∧ PairsFollow [next, ..more]

--| Neighbours that follow one another make a list of pieces that lexes: the lexer's look-ahead only ever looks at
--| the first character of the next piece.
theorem lexableOfPairs ∀ (pieces: List Piece)
    (plain: AllPlain pieces)
    (spelled: AllSpelled pieces)
    (pairs: PairsFollow pieces):
    Lexable pieces [] :=
  match pieces, plain, spelled, pairs with
    | [], plain, spelled, pairs => byComputing
    | [piece], Both pieceOk moreOk, Both spells moreSpelled, follows => Both spells (Both follows byComputing)
    | [piece, next, ..more], Both pieceOk (Both nextOk moreOk), Both spells later, Both follows laterPairs =>
      let tail := lexableOfPairs [next, ..more] (Both nextOk moreOk) later laterPairs
      let nextFollows: next.Follows (Parse.joinReads (pieceSteps more)) :=
        rewrite List.appendNil (Parse.joinReads (pieceSteps more)) at tail then tail.right.left
      let alike: StartsAlike next.chars (Parse.joinReads (pieceSteps [next, ..more]) ++ []) :=
        rewrite List.appendNil (Parse.joinReads (pieceSteps [next, ..more])) then
          alikeAppend next (Parse.joinReads (pieceSteps more)) nextOk later.left nextFollows
      Both spells
        (Both (followsAlike piece next.chars (Parse.joinReads (pieceSteps [next, ..more]) ++ []) alike follows) tail)

--| `lexPrinted`, as the printer's proofs will use it: pieces that are spelled as the lexer reads them, each of which
--| may be followed by the next, lex to the leaves of their layout.
theorem lexPrintedPairs ∀ (pieces: List Piece)
    (plain: AllPlain pieces)
    (spelled: AllSpelled pieces)
    (pairs: PairsFollow pieces):
    lex (piecesText pieces)
      = Ok {
        leaves = (pieces.foldLeft Laid.start Laid.lay).leaves.reverse,
        end = {
          leading = (pieces.foldLeft Laid.start Laid.lay).pending.reverse,
          blankLines = (pieces.foldLeft Laid.start Laid.lay).blankRun,
          trailing = None
        }
      } :=
  lexPieces pieces plain (lexableOfPairs pieces plain spelled pairs)
