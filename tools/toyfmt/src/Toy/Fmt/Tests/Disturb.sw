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

--| `text` with its layout disturbed by `seed`.
def disturb (text: Text) (seed: Nat): Text :=
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
          let (disturbed, after) := disturbChunk body rolled
          (out ++ [List.replicate blanks "\n" |> .joinWith "", disturbed, "\n"], after)))
  pieces.joinWith ""

def disturbChunk (text: Text) (dice: Dice): (Text, Dice) :=
  let (stretch, dice) := dice.roll 3
  let (shift, dice) := dice.roll 4
  let pieces := scan text |> reindent (stretch + 1) shift
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
