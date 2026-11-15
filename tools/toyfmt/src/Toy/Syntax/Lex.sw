--| Sprig's lexer: the source cut into lexemes with `Parse` over characters,
--| then the lexemes made into tokens that carry their layout and comments.
--|
--| Every character belongs to some lexeme, spaces and line breaks
--| included, so the lexemes' slices joined are the source. Only an
--| unclosed string fails to lex: a character no token is made of becomes a
--| `Stray` token, which the parser then reports where it stands.

namespace Toy.Syntax
import Std (Empty, Fail, List, Option, Parse, Result, Text)

--| A run of the source, before it is a token.
type Lexeme =
  | Spaces
  | LineBreak
  | CommentLexeme
  | WordLexeme
  | DigitsLexeme
  | StringLexeme
  | SignLexeme
  | SymbolsLexeme
  | StrayLexeme

def isWordStart (char: Char): Bool := char.isAsciiLetter || char == '_'

def isWordChar (char: Char): Bool := char.isAsciiAlphanumeric || char == '_'

def isOperatorChar (char: Char): Bool := "=|&!<+-*/%".any (symbol => symbol == char)

--| The lexeme at the start of `rest`, the input left, chosen by its first
--| characters.
def lexemeAt (rest: List Char): {Parse Char} Lexeme := match rest with
  | [' ', .._] =>
    let spaces := Parse.span (char => char == ' ')
    Spaces
  | ['\n', .._] =>
    let lineBreak := Parse.next (char => True)
    LineBreak
  | ['-', '-', .._] =>
    let comment := Parse.span (char => char != '\n')
    CommentLexeme
  | ['"', .._] =>
    stringLexeme()
    StringLexeme
  | [char, .._] if isWordStart char =>
    let word := Parse.span isWordChar
    WordLexeme
  | [char, .._] if char.isAsciiDigit =>
    let digits := Parse.span (char => char.isAsciiDigit)
    DigitsLexeme
  | [char, .._] if (punctuation char).isSome =>
    let sign := Parse.next (char => True)
    SignLexeme
  | [char, .._] if isOperatorChar char =>
    let run := Parse.many operatorChar
    SymbolsLexeme
  | [_, .._] =>
    let stray := Parse.next (char => True)
    StrayLexeme
  | [] => Parse.expected "a token"

--| One character of an operator run; a run stops before a comment's `--`.
def operatorChar(): {Parse Char} () := match Parse.mark().rest with
  | ['-', '-', .._] => Empty.absurd Parse.stop()
  | [char, .._] if isOperatorChar char =>
    let read := Parse.next (char => True)
    ()
  | _ => Empty.absurd Parse.stop()

--| A string, which must close on the line it starts on: plain runs and
--| the escapes `\"`, `\\` and `\n` between quotes.
def stringLexeme(): {Parse Char} () :=
  Parse.char '"'
  let segments := Parse.many (() =>
    match Parse.mark().rest with
      | ['\\', .._] =>
        Parse.char '\\'
        let escaped := Parse.satisfy "'\"', '\\' or 'n' after '\\'" (char => char == '"' || char == '\\' || char == 'n')
        ()
      | [char, .._] if char != '"' && char != '\n' =>
        let plain := Parse.span (char => char != '"' && char != '\\' && char != '\n')
        ()
      | _ => Empty.absurd Parse.stop())
  match Parse.next (char => char == '"') with
    | Some _ => ()
    | None => Parse.expected "'\"' to close the string"

--| The source as lexemes, every character in one. A lexeme fails only on a
--| bad string, which fails the lex anyway, so `Parse.locatedToEnd` needs no
--| handler to back up from one.
def lexemes(): {Parse Char} List (Parse.Located Lexeme) := Parse.locatedToEnd lexemeAt

--| The tokens so far (newest first), the trivia waiting for the next token
--| (newest first), where the current line starts, and whether it has had
--| anything but spaces yet.
type Assembly = {
  tokens: List (Parse.Located Token),
  pending: List Trivia,
  lineStart: Nat,
  lineEmpty: Bool
}

def Assembly.start: Assembly := { tokens = [], pending = [], lineStart = 0, lineEmpty = True }

--| The source's lexemes as tokens, each with its layout and comments, and
--| the own-line comments and blank lines after the last token, to the end of
--| the file (all of the file's, if it has no tokens).
def assemble (source: Text) (lexemes: List (Parse.Located Lexeme)): (List (Parse.Located Token), List Trivia) :=
  let done := lexemes.foldLeft Assembly.start (assembly lexeme => assembly.add source lexeme)
  (done.tokens.reverse, done.pending.reverse)

def cut (source: Text) (located: Parse.Located a): Text := source.slice located.offset (located.offset + located.length)

def Assembly.add (assembly: Assembly) (source: Text) (lexeme: Parse.Located Lexeme): Assembly := match lexeme.value with
  | Spaces => assembly
  | LineBreak =>
    let pending := if assembly.lineEmpty then addBlank assembly.pending else assembly.pending
    { assembly | pending, lineStart = lexeme.offset + 1, lineEmpty = True }
  | CommentLexeme =>
    let comment: Comment := { text = cut source lexeme }
    if assembly.lineEmpty then { assembly | pending = [OwnLine comment, ..assembly.pending], lineEmpty = False }
    else
      let located := { value = comment, offset = lexeme.offset, length = lexeme.length }
      { assembly | tokens = withTrailing assembly.tokens located }
  | kind =>
    let token := {
      value = {
        kind = lexemeKind kind (cut source lexeme),
        startsLine = assembly.lineEmpty,
        column = lexeme.offset - assembly.lineStart,
        above = assembly.pending.reverse,
        trailing = None
      },
      offset = lexeme.offset,
      length = lexeme.length
    }
    { assembly | tokens = [token, ..assembly.tokens], pending = [], lineEmpty = False }

--| Several empty lines in a row are one blank line.
def addBlank: List Trivia → List Trivia
  | [BlankLine, ..rest] => [BlankLine, ..rest]
  | pending => [BlankLine, ..pending]

--| The comment after the newest token, on its line. A comment that isn't
--| alone on its line always follows a token.
def withTrailing (tokens: List (Parse.Located Token)) (comment: Parse.Located Comment): List (Parse.Located Token) :=
  match tokens with
    | [last, ..earlier] => [{ last | value = { last.value | trailing = Some comment } }, ..earlier]
    | [] => []

def lexemeKind (lexeme: Lexeme) (text: Text): Kind := match lexeme with
  | WordLexeme => wordKind text
  | DigitsLexeme => Number text
  | StringLexeme => Str text
  | SignLexeme =>
    match text.toList with
      | [char] => punctuation char |> .map Sign |> .getOrElse (Stray text)
      | _ => Stray text
  | SymbolsLexeme => symbolsKind text
  | _ => Stray text

--| What lexing a source gave: its lexemes, every character in one, the
--| tokens made from them, and the own-line comments and blank lines after
--| the last token (all of the file's, if it has none).
type Lexed = {
  lexemes: List (Parse.Located Lexeme),
  tokens: List (Parse.Located Token),
  endTrivia: List Trivia
}

--| Whether the lexemes' slices of `source`, joined, are `source`: no
--| character lost, repeated or moved.
def covers (source: Text) (found: List (Parse.Located Lexeme)): Bool :=
  Text.concat (found.map (lexeme => cut source lexeme)) == source

--| The source lexed, then checked before it is answered: the lexemes'
--| slices joined must be the source (`covers`), so `lexCovers` is a
--| theorem about this definition and not about the lexer's loop. A source
--| that doesn't lex (an unclosed string, say) is the lexer's message.
def lex (source: Text): Result Lexed Text := match Fail.toResult (() => Parse.all source lexemes) with
  | Err message => Err message
  | Ok found =>
    if covers source found then
      let (tokens, endTrivia) := assemble source found
      Ok { lexemes = found, tokens, endTrivia }
    else Err "internal error: the lexemes don't add up to the source"
