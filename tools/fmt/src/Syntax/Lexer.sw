--| Stitchwort's lexer, matching `crates/syntax`'s `lex_with_trivia`: the
--| source cut into lexemes with `Parse` over characters, then the lexemes
--| made into tokens that carry their layout and comments (`assemble`).
--|
--| Every character belongs to some lexeme, spaces and line breaks
--| included, so the lexemes' slices joined are the source. A lexical error
--| stops the lex at once (`Parse.fatal`) with the Rust lexer's message, so
--| a refusal reads the same on both sides. Where the Rust lexer looks ahead
--| (a `"""` text is scanned whole before its tokens are made), the errors
--| are reported in the order it reports them.

namespace Syntax
import Std (Bool, Char, Empty, List, Nat, Option, Parse, Result, Text)

--| A run of the source, before layout is worked out.
type Lexeme = | Spaces | LineBreak | CommentLexeme | TokenLexeme (kind: Tok)

--| Where the lexer is reading: at the top of the file, or in the `${…}` of
--| a text literal. `block` says whether the innermost literal is a `"""`
--| one, and `scanning` whether any enclosing literal is: the Rust lexer
--| reads a `"""` text's `${…}`s in a scan of their own, whose errors differ.
type Place = | TopLevel | Inside (block: Bool) (scanning: Bool)

def Place.scanning: Place → Bool
  | TopLevel => False
  | Inside _ scanning => scanning

def Place.isInside: Place → Bool
  | TopLevel => False
  | Inside _ _ => True

-- The lexical errors, worded as the Rust lexer words them.

def unclosedString: Text := "this string isn't closed with `\"`"

def unclosedInterpolation: Text := "this `\${…}` isn't closed with `}`"

def blockInterpolationOneLine: Text := "a `\${…}` in a `\"\"\"` text stays on one line"

def commentTakesBrace: Text := "a comment in a `\${…}` runs to the end of the line, so it takes the `}`"

def blockInBlockInterpolation: Text :=
  "a `\${…}` in a `\"\"\"` text stays on one line, so it can't hold a `\"\"\"` text"

def unclosedBlock: Text := "this text isn't closed with `\"\"\"`"

def blockOpeningLine: Text :=
  "a `\"\"\"` text starts on the next line: nothing may follow the opening `\"\"\"` (use `\"…\"` for one line)"

def blockTab: Text := "tabs aren't allowed in a `\"\"\"` text's indentation; indent with spaces"

def tabs: Text := "tabs aren't allowed; indent with spaces"

def unclosedChar: Text := "this character isn't closed with `'`"

def charHoldsOne: Text := "a character literal holds exactly one character"

def strayAt: Text := "unexpected character `@`: it's only used in `@[…]`, which writes attributes"

def unknownEscape: Text := "unknown escape: use `\\n`, `\\t`, `\\r`, `\\\\`, `\\\"`, `\\'`, `\\$` or `\\u{…}`"

def badUnicodeEscape: Text := "`\\u{…}` takes 1 to 6 hexadecimal digits in braces"

def unexpected (char: Char): Text := "unexpected character ${shown char}"

-- Characters.

def isWordStart (char: Char): Bool := char.isAsciiLetter || char == '_'

def isWordChar (char: Char): Bool := char.isAsciiAlphanumeric || char == '_' || char == '\''

def isHexDigit (char: Char): Bool := char.isAsciiDigit || ('a' <= char && char <= 'f') || ('A' <= char && char <= 'F')

def hexValue (char: Char): Nat :=
  if char.isAsciiDigit then char.toNat - 48
  else if 'a' <= char && char <= 'f' then char.toNat - 87
  else char.toNat - 55

--| The number a run of hexadecimal digits spells.
def hexNumber (digits: List Char): Nat := digits.foldLeft 0 (value digit => value * 16 + hexValue digit)

--| The length of the escape at the start of `rest` (which starts with
--| `\`), or the error for it.
def escapeLength (rest: List Char): Result Nat Text := match rest with
  | ['\\', 'n', .._] |
      ['\\', 't', .._] |
      ['\\', 'r', .._] |
      ['\\', '\\', .._] |
      ['\\', '"', .._] |
      ['\\', '\'', .._] |
      ['\\', '$', .._] => Ok 2
  | ['\\', 'u', '{', ..after] =>
    let digits := after.takeWhile isHexDigit
    let closed := (after.drop digits.length).head == Some '}'
    if !closed || digits.isEmpty || digits.length > 6 then Err badUnicodeEscape
    else
      let code := hexNumber digits
      if Char.isScalar code then Ok (digits.length + 4)
      else Err "U+${upperHex code} isn't a Unicode scalar value, so it can't be a character"
  | ['\\', 'u', .._] => Err badUnicodeEscape
  | _ => Err unknownEscape

-- Reading.

def fail (message: Text): {Parse Char} a := Empty.absurd (Parse.fatal message)

def stop(): {Parse Char} a := Empty.absurd Parse.stop()

--| Reads `count` characters, whatever they are.
def skip (count: Nat): {Parse Char} () := match count with
  | Zero => ()
  | Succ more =>
    let read := Parse.next (char => True)
    skip more

--| What was read since `from`, as a lexeme.
def located (value: Lexeme) (from: Parse.Mark Char): {Parse Char} Parse.Located Lexeme :=
  let to := Parse.mark()
  { value, offset = from.offset, length = to.offset - from.offset }

--| Reads `count` characters as a token of kind `kind`.
def tokenOf (kind: Tok) (count: Nat): {Parse Char} Parse.Located Lexeme :=
  let from := Parse.mark()
  skip count
  located (TokenLexeme kind) from

--| A run of punctuation or operator characters at the start of `rest`, and
--| its length. `.` is read apart (`dots`), and `--` is a comment.
def symbol (rest: List Char): Option (Tok, Nat) := match rest with
  | ['(', .._] => Some (LParen, 1)
  | [')', .._] => Some (RParen, 1)
  | ['[', .._] => Some (LBracket, 1)
  | [']', .._] => Some (RBracket, 1)
  | ['{', .._] => Some (LBrace, 1)
  | ['}', .._] => Some (RBrace, 1)
  | [',', .._] => Some (Comma, 1)
  | [';', .._] => Some (Semi, 1)
  | [':', '=', .._] => Some (ColonEq, 2)
  | [':', .._] => Some (Colon, 1)
  | ['=', '=', .._] => Some (EqEq, 2)
  | ['=', '>', .._] => Some (FatArrow, 2)
  | ['=', .._] => Some (Equals, 1)
  | ['|', '|', .._] => Some (OrOr, 2)
  | ['|', '>', .._] => Some (PipeGt, 2)
  | ['|', .._] => Some (Pipe, 1)
  | ['&', '&', .._] => Some (AndAnd, 2)
  | ['+', '+', .._] => Some (PlusPlus, 2)
  | ['+', .._] => Some (Plus, 1)
  | ['-', '>', .._] => Some (Arrow, 2)
  | ['-', .._] => Some (Minus, 1)
  | ['*', .._] => Some (Star, 1)
  | ['/', .._] => Some (Slash, 1)
  | ['%', .._] => Some (Percent, 1)
  | ['!', '=', .._] => Some (NotEq, 2)
  | ['!', 'i', 'n', next, .._] if !isWordChar next => Some (NotIn, 3)
  | ['!', 'i', 'n'] => Some (NotIn, 3)
  | ['!', .._] => Some (Bang, 1)
  | ['<', '-', '>', .._] => Some (IffArrow, 3)
  | ['<', '=', .._] => Some (Le, 2)
  | ['<', .._] => Some (Lt, 1)
  | ['>', '=', .._] => Some (Ge, 2)
  | ['>', .._] => Some (Gt, 1)
  | ['?', .._] => Some (Question, 1)
  | ['@', '[', .._] => Some (At, 1)
  | _ => None

--| A name or keyword. `afterDot` says a `.` comes just before it, where
--| `exists` and `forall` are names (`x.exists p`).
def word (afterDot: Bool): {Parse Char} Parse.Located Lexeme := wordFrom afterDot Parse.mark()

--| `word` from the mark where it starts (a function of its own so that the proofs can name it).
def wordFrom (afterDot: Bool) (from: Parse.Mark Char): {Parse Char} Parse.Located Lexeme :=
  let first := Parse.span isWordChar
  let firstUpper := first.head.map (char => char.isAsciiUppercase) |> .getOrElse False
  let kind := match qualified (from.left + 1) firstUpper None with
    | Some lastUpper => if lastUpper then Upper else Lower
    | None => wordKind afterDot (Text.fromList first)
  located (TokenLexeme kind) from

--| The rest of a qualified name, `List.map` or `Std.List.Cons`: components
--| after an uppercase one, joined by `.` with no spaces. Whether the last
--| component read is uppercase, if any was.
def qualified (fuel: Nat) (upper: Bool) (found: Option Bool): {Parse Char} Option Bool := match fuel with
  | Zero => found
  | Succ more => qualifiedOn more upper found Parse.mark().rest

--| `qualified` with `more` fuel left, where the input is `input`.
def qualifiedOn (more: Nat) (upper: Bool) (found: Option Bool) (input: List Char): {Parse Char} Option Bool :=
  match input with
    | ['.', next, .._] if upper && next.isAsciiLetter =>
      skip 1
      let component := Parse.span isWordChar
      qualified more next.isAsciiUppercase (Some next.isAsciiUppercase)
    | _ => found

def wordKind (afterDot: Bool) (word: Text): Tok := match word with
  | "_" => Underscore
  | "exists" | "forall" if afterDot => Lower
  | "Type" => TypeU
  | "Prop" => PropU
  | _ =>
    match Tok.keyword word with
      | Some keyword => keyword
      | None => if word.toList.head.map Char.isAsciiUppercase |> .getOrElse False then Upper else Lower

--| A number: digits, then a fraction and an exponent unless a `.` comes
--| just before it (`xs.0.1` is `xs`, `.`, `0`, `.`, `1`).
def number (afterDot: Bool): {Parse Char} Parse.Located Lexeme := numberFrom afterDot Parse.mark()

--| `number` from the mark where it starts (a function of its own so that the proofs can name it).
def numberFrom (afterDot: Bool) (from: Parse.Mark Char): {Parse Char} Parse.Located Lexeme :=
  let digits := Parse.span Char.isAsciiDigit
  let float := numberTail afterDot
  located (TokenLexeme (if float then Float else Num)) from

--| What follows a number's digits: whether a fraction or an exponent made it a float.
def numberTail (afterDot: Bool): {Parse Char} Bool :=
  if afterDot then False
  else
    let fraction := fractionPart()
    let exponent := exponentPart()
    fraction || exponent

def fractionPart(): {Parse Char} Bool := fractionFrom Parse.mark()

def fractionFrom (at: Parse.Mark Char): {Parse Char} Bool :=
  if fractionAhead at.rest then
    skip 1
    let decimals := Parse.span Char.isAsciiDigit
    True
  else False

def exponentPart(): {Parse Char} Bool := exponentFrom Parse.mark()

def exponentFrom (at: Parse.Mark Char): {Parse Char} Bool := match exponentSkip at.rest with
  | Some count =>
    skip count
    let power := Parse.span Char.isAsciiDigit
    True
  | None => False

--| Whether a `.` and a digit come next: the fraction of a number.
def fractionAhead (input: List Char): Bool := match input with
  | ['.', next, .._] => next.isAsciiDigit
  | _ => False

--| The characters to skip before the digits of an exponent that comes next, `e` or `E`, then perhaps a sign.
def exponentSkip (input: List Char): Option Nat := match input with
  | [e, sign, next, .._] if (e == 'e' || e == 'E') && (sign == '+' || sign == '-') && next.isAsciiDigit => Some 2
  | [e, next, .._] if (e == 'e' || e == 'E') && next.isAsciiDigit => Some 1
  | _ => None

--| `.`, `..`, `..<` or `..=`, and after `.` or `..` the number or name
--| that follows it with no space.
def dots(): {Parse Char} List (Parse.Located Lexeme) :=
  let (kind, count) := match Parse.mark().rest with
    | ['.', '.', '<', .._] => (DotDotLt, 3)
    | ['.', '.', '=', .._] => (DotDotEq, 3)
    | ['.', '.', .._] => (DotDot, 2)
    | _ => (Dot, 1)
  let dot := tokenOf kind count
  if count == 3 then [dot]
  else
    match Parse.mark().rest with
      | [next, .._] if next.isAsciiDigit => [dot, number True]
      | [next, .._] if isWordStart next => [dot, word True]
      | _ => [dot]

--| A character literal, holding exactly one character or escape.
def charLiteral(): {Parse Char} Parse.Located Lexeme :=
  let from := Parse.mark()
  skip 1
  let counts := Parse.many charPiece
  match Parse.mark().rest with
    | ['\'', .._] =>
      skip 1
      if counts.sum == 1 then located (TokenLexeme CharLit) from else fail charHoldsOne
    | _ => fail unclosedChar

--| A run of a character literal's characters, or one escape: how many
--| characters it stands for.
def charPiece(): {Parse Char} Nat := match Parse.mark().rest with
  | ['\\', .._] => readEscape Parse.mark().rest
  | ['\'', .._] | ['\n', .._] | [] => stop()
  | _ => Parse.span (char => char != '\'' && char != '\\' && char != '\n') |> .length

--| Reads the escape `rest` starts with, failing with its error.
def readEscape (rest: List Char): {Parse Char} Nat := match escapeLength rest with
  | Ok count =>
    skip count
    1
  | Err message => fail message

-- Text literals.

--| A text literal from its opening quote: one `Str` token, or for an
--| interpolated one `StrStart`, then for each `${…}` an `InterpOpen`, its
--| tokens and an `InterpClose`, then `StrMid` pieces between and a
--| `StrEnd`.
def textLiteral (self: Place → {Parse Char} List (Parse.Located Lexeme)) (source: Text) (place: Place):
    {Parse Char} List (Parse.Located Lexeme) :=
  let from := Parse.mark()
  match from.rest with
    | ['"', '"', '"', .._] =>
      if place.scanning then fail blockInBlockInterpolation
      else
        skip 3
        let gap := Parse.span (char => char == ' ' || char == '\r')
        match Parse.mark().rest with
          | ['\n', .._] =>
            skip 1
            let body := Parse.mark().offset
            pieces (from.left + 1) self source place True body True from None []
          | [] => fail unclosedBlock
          | _ => fail blockOpeningLine
    | _ =>
      skip 1
      pieces (from.left + 1) self source place False 0 True from None []

--| The literal's pieces from `pieceStart`, after the `}` of a `${…}` (or
--| at the opening quote, when `first`). `found` is newest first; `escape`
--| is the first bad escape of a `"""` text, reported once the text has
--| been scanned to its end, as the Rust lexer does; `body` is where such a
--| text's lines start.
def pieces (fuel: Nat) (self: Place → {Parse Char} List (Parse.Located Lexeme)) (source: Text) (place: Place)
    (block: Bool) (body: Nat) (first: Bool) (pieceStart: Parse.Mark Char)
    (escape: Option Text) (found: List (Parse.Located Lexeme)):
    {Parse Char} List (Parse.Located Lexeme) :=
  match fuel with
    | Zero => fail "the lexer read a text literal without moving"
    | Succ more =>
      let segments := Parse.many (() => segment block)
      let escape := escape.orElse (segments.findMap (problem => problem))
      let at := Parse.mark()
      match at.rest with
        | ['$', '{', .._] =>
          let piece := located (TokenLexeme (if first then StrStart else StrMid)) pieceStart
          let withPiece := if first || piece.length > 0 then [piece, ..found] else found
          let open := tokenOf InterpOpen 2
          let inner := self (Inside block (block || place.scanning))
          let close := tokenOf InterpClose 1
          let after := Parse.mark()
          pieces more self source place block body False after escape ([close, ..inner.reverse] ++ [open, ..withPiece])
        | ['"', '"', '"', .._] if block => closeBlock source body escape first pieceStart found
        | ['"', .._] if !block =>
          skip 1
          let piece := located (TokenLexeme (if first then Str else StrEnd)) pieceStart
          [piece, ..found].reverse
        | _ => fail (if block then unclosedBlock else unclosedString)

--| The closing `"""` of a text, and the checks the Rust lexer makes once it
--| has scanned the text: tabs in the indentation, then bad escapes.
def closeBlock (source: Text) (body: Nat) (escape: Option Text) (first: Bool)
    (pieceStart: Parse.Mark Char) (found: List (Parse.Located Lexeme)):
    {Parse Char} List (Parse.Located Lexeme) :=
  let close := Parse.mark().offset
  skip 3
  if tabbedIndent (source.slice body close) then fail blockTab
  else
    match escape with
      | Some message => fail message
      | None =>
        let piece := located (TokenLexeme (if first then Str else StrEnd)) pieceStart
        [piece, ..found].reverse

--| Whether a `"""` text's lines (from its body to its closing quotes) have
--| a tab right after their indentation. Blank lines are skipped, except
--| the closing line.
def tabbedIndent (lines: Text): Bool :=
  let all := lines.split '\n'
  let count := all.length
  all.withIndex.any ((index, line) =>
    let blank := line.all (char => char == ' ' || char == '\t' || char == '\r')
    if blank && index + 1 < count then False else (line.toList.dropWhile (char => char == ' ')).head == Some '\t')

--| A run of a text literal's characters between its quotes: for a `"""`
--| text, the error of an escape in it, if any, which waits until the text
--| has been scanned; a `"` string's bad escape stops the lex at once.
def segment (block: Bool): {Parse Char} Option Text := match Parse.mark().rest, block with
  | ['$', '{', .._], _ => stop()
  | ['\\', .._], False =>
    let count := readEscape Parse.mark().rest
    None
  | ['\\', next, .._], True =>
    let problem := escapeLength Parse.mark().rest
    skip (if next == '\n' then 1 else 2)
    match problem with
      | Ok _ => None
      | Err message => Some message
  | ['\\'], True =>
    skip 1
    Some unknownEscape
  | ['"', '"', '"', .._], True => stop()
  | ['"', .._] | ['\n', .._], False => stop()
  | [], _ => stop()
  | ['$', .._], _ =>
    skip 1
    None
  | ['"', .._], True =>
    skip 1
    None
  | _, _ =>
    let run := Parse.span (char => char != '"' && char != '\\' && char != '$' && (block || char != '\n'))
    None

-- The lexemes.

--| One lexeme, or several for a text literal or a `{…}` inside a `${…}`;
--| it stops (reading nothing) at the end of the file, or inside a `${…}` at
--| its `}`.
def item (self: Place → {Parse Char} List (Parse.Located Lexeme)) (source: Text) (place: Place):
    {Parse Char} List (Parse.Located Lexeme) :=
  itemAt self source place Parse.mark()

--| `item` from the mark where it starts (a function of its own so that the
--| proofs can name it).
def itemAt (self: Place → {Parse Char} List (Parse.Located Lexeme)) (source: Text)
    (place: Place) (from: Parse.Mark Char):
    {Parse Char} List (Parse.Located Lexeme) :=
  itemOn self source place from from.rest

--| `item` from the mark `from`, whose input is `input`.
def itemOn (self: Place → {Parse Char} List (Parse.Located Lexeme)) (source: Text) (place: Place)
    (from: Parse.Mark Char) (input: List Char):
    {Parse Char} List (Parse.Located Lexeme) :=
  match input with
    | [] =>
      match place with
        | TopLevel => stop()
        | Inside _ scanning => fail (if scanning then unclosedInterpolation else unclosedString)
    | ['\n', .._] =>
      match place with
        | TopLevel =>
          skip 1
          [located LineBreak from]
        | Inside block _ => fail (if block then blockInterpolationOneLine else unclosedString)
    | ['}', .._] if place.isInside => stop()
    | ['{', .._] if place.isInside =>
      let open := tokenOf LBrace 1
      let inner := self place
      let close := tokenOf RBrace 1
      [open, ..inner] ++ [close]
    | [' ', .._] | ['\r', .._] =>
      let run := Parse.span (char => char == ' ' || char == '\r')
      [located Spaces from]
    | ['\t', .._] => fail tabs
    | ['-', '-', .._] =>
      let text := Parse.span (char => char != '\n')
      match place, Parse.mark().rest with
        | Inside True _, ['\n', .._] => fail commentTakesBrace
        | Inside True _, [] => fail unclosedInterpolation
        | _, _ => [located CommentLexeme from]
    | ['"', .._] => textLiteral self source place
    | ['\'', .._] => [charLiteral()]
    | ['.', .._] => dots()
    | [next, .._] if isWordStart next => [word False]
    | [next, .._] if next.isAsciiDigit => [number False]
    | [next, .._] if next.toNat >= 128 =>
      match Tok.unicodeAlias next with
        | Some kind => [tokenOf kind 1]
        | None => fail (unexpected next)
    | [next, .._] =>
      match symbol input with
        | Some (kind, count) => [tokenOf kind count]
        | None => fail (if next == '@' then strayAt else unexpected next)

--| The lexemes from here to the end of the file, or inside a `${…}` to its
--| closing `}`.
def lexemesIn (source: Text) (place: Place): {Parse Char} List (Parse.Located Lexeme) :=
  Parse.recursiveWith (self inner => Parse.many (() => item self source inner) |> List.concat) place

--| The source's lexemes, every character in one, or the lexical error.
def lexemes (source: Text): Result (List (Parse.Located Lexeme)) Text :=
  match Parse.run source.toList (() => lexemesIn source TopLevel) with
    | Ok found => Ok found
    | Err failure => Err (failure.messages.head.getOrElse "the lexer stopped without a message")

-- Layout: the lexemes made into tokens.

--| The leaves so far (newest first), the own-line comments waiting for the
--| next token (newest first) and the blank lines before them, whether the
--| current line has had a token or comment, whether no token has started
--| it yet, the bytes read, and the byte where the current line starts.
type Assembly = {
  leaves: List Leaf,
  pending: List Comment,
  blankRun: Nat,
  lineBlank: Bool,
  freshLine: Bool,
  bytes: Nat,
  lineStart: Nat
}

def Assembly.start: Assembly :=
  { leaves = [], pending = [], blankRun = 0, lineBlank = True, freshLine = True, bytes = 0, lineStart = 0 }

--| The characters without the `\r`s and spaces that end them, in any order: a comment line ending `\r\r\n` or `\r \n`
--| would otherwise keep a `\r`, which the printer's `\r\n` reads back as none.
def trimReturns: List Char → List Char
  | [] => []
  | [char, ..rest] =>
    let kept := trimReturns rest
    if (char == '\r' || char == ' ') && kept.isEmpty then [] else [char, ..kept]

--| The comment's text without its trailing `\r`s and spaces.
def withoutReturn (text: Text): Text := Text.fromList (trimReturns text.toList)

--| The bytes after the last line break of a text, if it has one.
def afterLastBreak (text: Text): Option Nat := text.toList.foldLeft None (after char =>
  if char == '\n' then Some 0 else after.map (bytes => bytes + (Char.utf8 char).length))

def Assembly.add (assembly: Assembly) (source: Text) (lexeme: Parse.Located Lexeme): Assembly :=
  let text := source.slice lexeme.offset (lexeme.offset + lexeme.length)
  match lexeme.value with
    | Spaces => { assembly | bytes = assembly.bytes + lexeme.length }
    | LineBreak =>
      let bytes := assembly.bytes + 1
      let blankRun := if assembly.lineBlank then assembly.blankRun + 1 else assembly.blankRun
      { assembly | blankRun, lineBlank = True, freshLine = True, bytes, lineStart = bytes }
    | CommentLexeme =>
      let column := assembly.bytes - assembly.lineStart
      let bytes := assembly.bytes + text.utf8Length
      if assembly.freshLine then
        let comment: Comment := { text = withoutReturn text, column, blankLines = assembly.blankRun }
        { assembly | pending = [comment, ..assembly.pending], blankRun = 0, lineBlank = False, bytes }
      else
        let comment: Comment := { text = withoutReturn text, column, blankLines = 0 }
        { assembly | leaves = withTrailing assembly.leaves comment, bytes }
    | TokenLexeme kind =>
      let width := if text.all (char => char.toNat < 128) then lexeme.length else text.utf8Length
      let token: Token := { kind, text, column = assembly.bytes - assembly.lineStart, lineStart = assembly.freshLine }
      let trivia: Trivia := { leading = assembly.pending.reverse, blankLines = assembly.blankRun, trailing = None }
      let bytes := assembly.bytes + width
      let lineStart := match afterLastBreak text with
        | Some after => bytes - after
        | None => assembly.lineStart
      {
        leaves = [{ token, trivia }, ..assembly.leaves],
        pending = [],
        blankRun = 0,
        lineBlank = False,
        freshLine = False,
        bytes,
        lineStart
      }

--| The newest leaf with `comment` after it on its line. A comment that
--| isn't alone on its line always follows a token.
def withTrailing (leaves: List Leaf) (comment: Comment): List Leaf := match leaves with
  | [last, ..earlier] => [{ last | trivia = { last.trivia | trailing = Some comment } }, ..earlier]
  | [] => []

--| The source's lexemes as leaves, each token with its layout and trivia.
def assemble (source: Text) (lexemes: List (Parse.Located Lexeme)): Lexed :=
  let done := lexemes.foldLeft Assembly.start (assembly lexeme => assembly.add source lexeme)
  {
    leaves = done.leaves.reverse,
    end = { leading = done.pending.reverse, blankLines = done.blankRun, trailing = None }
  }

--| The source lexed, with every token's comments and blank lines as the
--| Rust lexer attaches them (before comment placement), or the lexical error.
def lex (source: Text): Result Lexed Text := match lexemes source with
  | Ok found => Ok (assemble source found)
  | Err message => Err message
