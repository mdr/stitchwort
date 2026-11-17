--| The disturber: from a seed, it changes a formatted Sprig text's layout
--| without changing its tree, so the printer can be tested to ignore the
--| author's layout: `format (disturb seed out) = out`. It re-indents each
--| declaration within the layout rule, doubles and squeezes spaces, joins
--| and splits lines inside brackets, and adds blank lines where the parser
--| drops them.
--|
--| It works on the text cut into pieces (spaces, line ends, words, operator
--| runs, punctuation, strings and comments), so it never touches what is
--| inside a string or a comment. What it may do, piece by piece:
--|
--| - Indentation: every line after a declaration's first moves from column
--|   `c` to `c * stretch + shift`. Equal columns stay equal and deeper ones
--|   deeper, so every block keeps its statements.
--| - Spaces: a space between two pieces on a line grows; it is squeezed out,
--|   or one is added where there was none, only beside a bracket, a comma or
--|   an operator, and never between two operators (`< -` would become `<-`),
--|   before a comment, around `.`, or before a call's `(`.
--| - Lines inside brackets, where line starts don't matter: a space becomes
--|   a line break, a line break and its indentation become a space, and a
--|   blank line is added; never next to a comment, which would move it.
--| - Blank lines: more where there was one, and one before a line deeper
--|   than the line above (a continuation, or a block's first statement),
--|   where the parser drops it.
--|
--| Five more changes alter the text but not the program, one for each
--| freedom the formatter's passes remove (toy-plus-plus.md §2); they make
--| `disturb` what `disturbLayout` is not, a change of tokens:
--|
--| - Spare brackets: a name or number in an expression is wrapped in a
--|   pair, unless a comment is beside it (the pair would hold it) or the
--|   word is a binder, a keyword, a field name or in a declaration's header.
--| - Parameter groups: `a b: T` becomes `a: T, b: T`.
--| - A trailing comma after the last item of a list, call or parameter list.
--| - `takes` is dropped from a header.
--| - A comment after a closer moves before it, onto the last line of what
--|   the closer ends (rule N moves it back).

namespace Toy.Fmt.Tests
import Std (List, Option, Text)

type Piece =
  | Gap (count: Nat)
  | LineEnd
  | WordPiece (text: Text)
  --| A run of operator characters, `&&` or `<=`.
  | SymbolRun (text: Text)
  | Punct (char: Char)
  --| A string, quotes included.
  | Quoted (text: Text)
  --| A comment, to the end of its line.
  | Remark (text: Text)

def Piece.text: Piece → Text
  | Gap count => " ".repeat count
  | LineEnd => "\n"
  | WordPiece text => text
  | SymbolRun text => text
  | Punct char => char.toText
  | Quoted text => text
  | Remark text => text

--| Neither a space nor a line end.
def Piece.isSignificant: Piece → Bool
  | Gap _ => False
  | LineEnd => False
  | _ => True

def Piece.isSymbolRun: Piece → Bool := matches | SymbolRun _

def Piece.isRemark: Piece → Bool := matches | Remark _

def Piece.isWord: Piece → Bool := matches | WordPiece _

def Piece.isBracketOrComma: Piece → Bool := matches | Punct ('(' | ')' | '[' | ']' | ',')

def isSymbolChar (char: Char): Bool := "+-*/%<=!&|>".any (symbol => symbol == char)

def isWordChar (char: Char): Bool := char.isAsciiAlphanumeric || char == '_'

def scan (text: Text): List Piece := scanChars text.length text.toList

--| Each step takes at least one character, so the length is enough fuel.
def scanChars (fuel: Nat) (chars: List Char): List Piece := match fuel, chars with
  | 0, _ => []
  | _, [] => []
  | Succ more, [' ', .._] =>
    let (gap, rest) := chars.span (char => char == ' ')
    [Gap gap.length, ..scanChars more rest]
  | Succ more, ['\n', ..rest] => [LineEnd, ..scanChars more rest]
  | Succ more, ['-', '-', .._] =>
    let (comment, rest) := chars.span (char => char != '\n')
    [Remark (Text.fromList comment), ..scanChars more rest]
  | Succ more, ['"', ..rest] =>
    let (body, after) := stringBody rest
    [Quoted (Text.fromList ['"', ..body]), ..scanChars more after]
  | Succ more, [char, .._] if isWordChar char =>
    let (word, rest) := chars.span isWordChar
    [WordPiece (Text.fromList word), ..scanChars more rest]
  | Succ more, [char, .._] if isSymbolChar char =>
    let (run, rest) := symbolRun chars
    [SymbolRun (Text.fromList run), ..scanChars more rest]
  | Succ more, [char, ..rest] => [Punct char, ..scanChars more rest]

--| A string's characters after its opening quote, up to and including the
--| closing one, and what follows.
def stringBody: List Char → (List Char, List Char)
  | [] => ([], [])
  | ['\\', escaped, ..rest] =>
    let (body, after) := stringBody rest
    (['\\', escaped, ..body], after)
  | ['"', ..rest] => (['"'], rest)
  | [char, ..rest] =>
    let (body, after) := stringBody rest
    ([char, ..body], after)

--| Operator characters up to a comment's `--`.
def symbolRun: List Char → (List Char, List Char)
  | ['-', '-', ..rest] => ([], ['-', '-', ..rest])
  | [char, ..rest] if isSymbolChar char =>
    let (run, after) := symbolRun rest
    ([char, ..run], after)
  | chars => ([], chars)

def render (pieces: List Piece): Text := pieces.map Piece.text |> .joinWith ""

--| What the disturber must keep: the pieces that aren't layout.
def significant (text: Text): List Text := scan text |> .filter Piece.isSignificant |> .map Piece.text

--| A deterministic stream of rolls from a seed (a linear congruential
--| generator, as C's `rand` was).
type Dice = { state: Nat }

def Dice.roll (dice: Dice) (sides: Nat): (Nat, Dice) :=
  let next := (dice.state * 1103515245 + 12345) % 2147483648
  (next / 65536 % sides, { state = next })

--| A declaration's lines, and how many blank lines were above it.
type LineGroup = { blanksBefore: Nat, lines: List Text }

--| The text's declarations: each starts at a line at column 0, and takes
--| the indented lines after it and the blank lines between them.
def chunks (text: Text): List LineGroup :=
  let (done, current, pending) :=
    text.lines.foldLeft
      (([], None, 0): (List LineGroup, Option LineGroup, Nat))
      (((done, current, pending) line =>
        if line.isEmpty then (done, current, pending + 1)
        else if line.startsWith " " then
          match current with
            | Some chunk => (done, Some { chunk | lines = chunk.lines ++ List.replicate pending "" ++ [line] }, 0)
            | None => (done, Some { blanksBefore = pending, lines = [line] }, 0)
        else
          let finished := match current with
            | Some chunk => [chunk, ..done]
            | None => done
          (finished, Some { blanksBefore = pending, lines = [line] }, 0)))
  let all := match current with
    | Some chunk => [chunk, ..done]
    | None => done
  all.reverse

--| One in `odds` of the places a change could be made takes it.
def defaultOdds: Nat := 4

--| `text` with its layout and its freedoms disturbed by `seed`: the five
--| changes of the tree's freedoms, then the layout.
def disturb (text: Text) (seed: Nat): Text := disturbWith defaultOdds True text seed

--| `text` with only its layout disturbed: the same tokens in the same order.
def disturbLayout (text: Text) (seed: Nat): Text := disturbWith defaultOdds False text seed

def disturbWith (odds: Nat) (freedoms: Bool) (text: Text) (seed: Nat): Text :=
  let start: Dice := { state = seed * 7919 + 17 }
  let (pieces, _) :=
    chunks text
      |> .foldLeft
        ([], start)
        (((out, dice) chunk =>
          let (blanks, rolled) :=
            if chunk.blanksBefore == 0 then (0, dice)
            else dice.roll 3 |> (((extra, next)) => (chunk.blanksBefore + extra, next))
          let body := chunk.lines.joinWith "\n"
          let (disturbed, after) := disturbChunk odds freedoms body rolled
          (out ++ [List.replicate blanks "\n" |> .joinWith "", disturbed, "\n"], after)))
  pieces.joinWith ""

def disturbChunk (odds: Nat) (freedoms: Bool) (text: Text) (dice: Dice): (Text, Dice) :=
  let (stretch, dice) := dice.roll 3
  let (shift, dice) := dice.roll 4
  let (changed, dice) := if freedoms then changeFreedoms odds dice (scan text) else (scan text, dice)
  let pieces := changed |> reindent (stretch + 1) shift
  let fuel := 3 * pieces.length + 3
  let (pieces, dice) := lines fuel dice 0 0 pieces
  let (pieces, dice) := blanks (3 * pieces.length + 3) dice 0 pieces
  let (pieces, dice) := spaces (3 * pieces.length + 3) dice pieces
  (render pieces, dice)

def reindent: (pieces: List Piece) → (stretch: Nat) → (shift: Nat) → List Piece
  | [LineEnd, Gap count, ..rest], stretch, shift =>
    [LineEnd, Gap (count * stretch + shift), ..reindent rest stretch shift]
  | [piece, ..rest], stretch, shift => [piece, ..reindent rest stretch shift]
  | [], _, _ => []

def bracketDepth (depth: Nat): Piece → Nat
  | Punct ('(' | '[') => depth + 1
  | Punct (')' | ']') => depth - 1
  | _ => depth

--| Joins and splits lines inside brackets, and adds blank lines there.
--| `depth` counts the brackets open after the pieces already done, and
--| `indent` is the current line's indentation.
def lines (fuel: Nat) (dice: Dice) (depth indent: Nat) (pieces: List Piece): (List Piece, Dice) :=
  match fuel, pieces with
    | 0, _ => (pieces, dice)
    | _, [] => ([], dice)
    | Succ more, [LineEnd, Gap count, ..rest] => lines more dice depth count [Gap count, ..rest] |> prepend LineEnd
    | Succ more, [LineEnd, ..rest] => lines more dice depth 0 rest |> prepend LineEnd
    | Succ more, [piece, Gap count, next, ..rest] if piece.isSignificant && next.isSignificant =>
      let inside := bracketDepth depth piece
      let (choice, dice) := dice.roll 3
      if inside > 0 && not next.isRemark && choice == 0 then
        let (extra, dice) := dice.roll 3
        let deeper := indent + 2 + extra
        lines more dice inside deeper [next, ..rest] |> prepend3 piece LineEnd (Gap deeper)
      else lines more dice inside indent [Gap count, next, ..rest] |> prepend piece
    | Succ more, [piece, LineEnd, Gap count, next, ..rest] if piece.isSignificant && next.isSignificant =>
      let inside := bracketDepth depth piece
      let (choice, dice) := dice.roll 4
      if inside > 0 && not piece.isRemark && not next.isRemark && choice == 0 then
        lines more dice inside indent [next, ..rest] |> prepend2 piece (Gap 1)
      else if inside > 0 && choice == 1 then
        lines more dice inside indent [LineEnd, Gap count, next, ..rest] |> prepend2 piece LineEnd
      else lines more dice inside indent [LineEnd, Gap count, next, ..rest] |> prepend piece
    | Succ more, [piece, ..rest] => lines more dice (bracketDepth depth piece) indent rest |> prepend piece

--| Adds blank lines where there is one already, and before a line deeper
--| than the one above. `indent` is the current line's indentation.
def blanks (fuel: Nat) (dice: Dice) (indent: Nat) (pieces: List Piece): (List Piece, Dice) := match fuel, pieces with
  | 0, _ => (pieces, dice)
  | _, [] => ([], dice)
  | Succ more, [LineEnd, LineEnd, ..rest] =>
    let (extra, dice) := dice.roll 2
    let (done, dice) := blanks more dice indent [LineEnd, ..rest]
    ([LineEnd, ..List.replicate extra LineEnd, ..done], dice)
  | Succ more, [LineEnd, Gap count, ..rest] =>
    let (choice, dice) := dice.roll 3
    let added := if count > indent && choice == 0 then [LineEnd] else []
    let (done, dice) := blanks more dice count rest
    ([LineEnd, ..added, Gap count, ..done], dice)
  | Succ more, [LineEnd, ..rest] => blanks more dice 0 rest |> prepend LineEnd
  | Succ more, [piece, ..rest] => blanks more dice indent rest |> prepend piece

--| Grows, squeezes and adds spaces between pieces on a line, and adds
--| spaces at the ends of lines.
def spaces (fuel: Nat) (dice: Dice) (pieces: List Piece): (List Piece, Dice) := match fuel, pieces with
  | 0, _ => (pieces, dice)
  | _, [] => ([], dice)
  | Succ more, [piece, Gap count, next, ..rest] if piece.isSignificant && next.isSignificant =>
    let (choice, dice) := dice.roll 4
    let gap := match choice with
      | 0 => [Gap (count + 1)]
      | 1 => [Gap (count + 2)]
      | 2 => if canSqueeze piece next then [] else [Gap count]
      | _ => [Gap count]
    let (done, dice) := spaces more dice [next, ..rest]
    ([piece, ..gap, ..done], dice)
  | Succ more, [piece, next, ..rest] if piece.isSignificant && next.isSignificant =>
    let (choice, dice) := dice.roll 3
    let gap := if choice == 0 && canSpace piece next then [Gap 1] else []
    let (done, dice) := spaces more dice [next, ..rest]
    ([piece, ..gap, ..done], dice)
  -- Not after a comment, which would take the spaces into its text.
  | Succ more, [piece, LineEnd, ..rest] if piece.isSignificant && not piece.isRemark =>
    let (choice, dice) := dice.roll 4
    let trailing := if choice == 0 then [Gap 1] else []
    let (done, dice) := spaces more dice [LineEnd, ..rest]
    ([piece, ..trailing, ..done], dice)
  | Succ more, [piece, ..rest] => spaces more dice rest |> prepend piece

--| Whether the space between two pieces can go without the pieces running
--| together into other tokens.
def canSqueeze (before after: Piece): Bool :=
  (before.isBracketOrComma || after.isBracketOrComma || before.isSymbolRun || after.isSymbolRun)
    && not (before.isSymbolRun && after.isSymbolRun)
    && not after.isRemark
    && not (isDot before || isDot after)

--| Whether a space can go between two pieces that touch: as for squeezing,
--| and not before a call's `(`.
def canSpace (before after: Piece): Bool :=
  canSqueeze before after && not (isOpenBracket after && (before.isWord || isCloseBracket before))

def isDot: Piece → Bool := matches | Punct '.'

def isOpenBracket: Piece → Bool := matches | Punct ('(' | '[')

def isCloseBracket: Piece → Bool := matches | Punct (')' | ']')

def prepend (done: (List Piece, Dice)) (piece: Piece): (List Piece, Dice) :=
  let (pieces, dice) := done
  ([piece, ..pieces], dice)

def prepend2 (done: (List Piece, Dice)) (first second: Piece): (List Piece, Dice) :=
  let (pieces, dice) := done
  ([first, second, ..pieces], dice)

def prepend3 (done: (List Piece, Dice)) (first second third: Piece): (List Piece, Dice) :=
  let (pieces, dice) := done
  ([first, second, third, ..pieces], dice)

-- The five changes of the tree's freedoms. Each works on a declaration's
-- pieces as the formatter wrote them, before the layout is disturbed, and
-- takes a place with probability 1 in `odds`.

def changeFreedoms (odds: Nat) (dice: Dice) (pieces: List Piece): (List Piece, Dice) :=
  let (pieces, dice) := moveCommentsBeforeClosers odds dice pieces
  let (pieces, dice) := splitGroups (3 * pieces.length + 3) odds dice pieces
  let (pieces, dice) := addTrailingCommas odds dice [] None None pieces
  let (pieces, dice) := dropTakes odds dice pieces
  wrapOperands odds dice { inBody = False, lineStart = True, before = None } pieces

def isKeyword (word: Text): Bool := ["let", "fn", "takes", "if", "then", "else"].any (keyword => keyword == word)

def Piece.isComma: Piece → Bool := matches | Punct ','

def Piece.isCloser: Piece → Bool := matches | Punct (')' | ']')

def Piece.isGap: Piece → Bool := matches | Gap _

--| The first piece that isn't layout.
def nextSignificant (pieces: List Piece): Option Piece := match pieces.dropWhile (piece => not piece.isSignificant) with
  | [piece, .._] => Some piece
  | [] => None

-- Change 5: a comment after a closer goes before it, on the line above it,
-- where it trails the last token inside. Rule N moves a comment on a closer
-- back to that token, so both spellings are one tree.

def moveCommentsBeforeClosers (odds: Nat) (dice: Dice): List Piece → (List Piece, Dice)
  | [] => ([], dice)
  | [before, ..tail] =>
    match tail with
      | [closer, Gap _, Remark text, ..rest] if before.isSignificant && not before.isRemark && closer.isCloser =>
        let (choice, dice) := dice.roll odds
        if choice == 0 then
          moveCommentsBeforeClosers odds dice rest |> prependAll [before, Gap 1, Remark text, LineEnd, Gap 2, closer]
        else moveCommentsBeforeClosers odds dice tail |> prepend before
      | _ => moveCommentsBeforeClosers odds dice tail |> prepend before

-- Change 2: a group of names becomes a group for each. A group starts after
-- `(` or `,`, and is names separated by spaces up to a `:` and a type.

--| The names, the type and what follows, for a group's names from the first.
def groupNames (names: List Text): List Piece → Option (List Text, Text, List Piece)
  | [WordPiece name, Gap _, ..rest] => groupNames (names ++ [name]) rest
  | [WordPiece name, Punct ':', Gap _, WordPiece annotation, ..rest] => Some (names ++ [name], annotation, rest)
  | _ => None

def eachGroup (annotation: Text): List Text → List Piece
  | [] => []
  | [name] => [WordPiece name, Punct ':', Gap 1, WordPiece annotation]
  | [name, ..rest] =>
    [WordPiece name, Punct ':', Gap 1, WordPiece annotation, Punct ',', Gap 1, ..eachGroup annotation rest]

def Piece.opensGroup: Piece → Bool := matches | Punct ('(' | ',')

def splitGroups (fuel odds: Nat) (dice: Dice) (pieces: List Piece): (List Piece, Dice) := match fuel, pieces with
  | 0, _ => (pieces, dice)
  | _, [] => ([], dice)
  | Succ more, [opener, ..rest] if opener.opensGroup =>
    let (gap, afterGap) := rest.span Piece.isGap
    match groupNames [] afterGap with
      | Some (names, annotation, after) if names.length >= 2 =>
        let (choice, dice) := dice.roll odds
        if choice == 0 then splitGroups more odds dice after |> prependAll [opener, ..gap, ..eachGroup annotation names]
        else splitGroups more odds dice rest |> prepend opener
      | _ => splitGroups more odds dice rest |> prepend opener
  | Succ more, [piece, ..rest] => splitGroups more odds dice rest |> prepend piece

-- Change 3: a comma after the last item of a list, call or parameter list,
-- put straight after the item. `stack` says, for each bracket open, whether
-- it holds items (a list, a call's arguments, parameters), not one
-- expression. `before` is the last piece that isn't layout, `raw` the
-- piece just before.

def opensItems (raw before: Option Piece) (piece: Piece): Bool := match piece with
  | Punct '[' => True
  | Punct '(' =>
    match raw, before with
      | Some (WordPiece word), _ => not (isKeyword word)
      | Some (Punct (')' | ']')), _ => True
      | _, Some (WordPiece "takes") => True
      | _, _ => False
  | _ => False

def addTrailingCommas (odds: Nat) (dice: Dice) (stack: List Bool) (raw before: Option Piece):
    List Piece → (List Piece, Dice)
  | [] => ([], dice)
  | [piece, ..rest] =>
    let stack := match piece with
      | Punct ('(' | '[') => [opensItems raw before piece, ..stack]
      | Punct (')' | ']') => stack.drop 1
      | _ => stack
    let next := if piece.isSignificant then Some piece else before
    let endsItem := match piece, nextSignificant rest, stack with
      | Punct ('(' | '[' | ','), _, _ => False
      | Remark _, _, _ => False
      | _, Some closer, [True, .._] => piece.isSignificant && closer.isCloser
      | _, _, _ => False
    let (choice, dice) := dice.roll odds
    let (done, dice) := addTrailingCommas odds dice stack (Some piece) next rest
    if endsItem && choice == 0 then ([piece, Punct ',', ..done], dice) else ([piece, ..done], dice)

-- Change 4: `fn name takes (` loses `takes`; with no comment beside it.

def dropTakes (odds: Nat) (dice: Dice): List Piece → (List Piece, Dice)
  | [] => ([], dice)
  | [WordPiece name, Gap _, WordPiece "takes", Gap _, Punct '(', ..rest] =>
    let (choice, dice) := dice.roll odds
    if choice == 0 then dropTakes odds dice rest |> prepend2 (WordPiece name) (Punct '(')
    else dropTakes odds dice rest |> prepend5 (WordPiece name) (Gap 1) (WordPiece "takes") (Gap 1) (Punct '(')
  | [piece, ..rest] => dropTakes odds dice rest |> prepend piece

-- Change 1: a name or number in an expression gets brackets.

type WrapState = { inBody: Bool, lineStart: Bool, before: Option Piece }

def WrapState.after (state: WrapState): Piece → WrapState
  | Gap _ => state
  | LineEnd => { state | lineStart = True }
  | SymbolRun "=" => { inBody = True, lineStart = False, before = Some (SymbolRun "=") }
  | piece => { state | lineStart = False, before = Some piece }

--| Whether `piece` is an operand a pair can wrap without holding a comment
--| or changing what the word is: not a binder, a keyword, a field name, at
--| the start of a line (where it could start a statement) or in the
--| header.
def WrapState.wrappable (state: WrapState) (piece: Piece) (rest: List Piece): Bool := match piece with
  | WordPiece word =>
    state.inBody
      && not state.lineStart
      && not (isKeyword word)
      && (match state.before with
        | Some (WordPiece ("let" | "fn")) => False
        | Some (Punct '.') => False
        | Some (Remark _) => False
        | _ => True)
      && (match rest with
        | [Punct '.', .._] => False
        | [Gap _, Remark _, .._] => False
        | [Remark _, .._] => False
        | _ => True)
  | _ => False

def wrapOperands (odds: Nat) (dice: Dice) (state: WrapState): List Piece → (List Piece, Dice)
  | [] => ([], dice)
  | [piece, ..rest] =>
    let (choice, dice) := dice.roll odds
    let after := state.after piece
    if choice == 0 && state.wrappable piece rest then
      wrapOperands odds dice after rest |> prepend3 (Punct '(') piece (Punct ')')
    else wrapOperands odds dice after rest |> prepend piece

def prepend5 (done: (List Piece, Dice)) (first second third fourth fifth: Piece): (List Piece, Dice) :=
  let (pieces, dice) := done
  ([first, second, third, fourth, fifth, ..pieces], dice)

def prependAll (done: (List Piece, Dice)) (added: List Piece): (List Piece, Dice) :=
  let (pieces, dice) := done
  (added ++ pieces, dice)
