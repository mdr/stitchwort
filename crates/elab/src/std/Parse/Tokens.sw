import Parse.Problem (Expected, Literal, Literals, Message)
import Parse.Tests.Tok (Number, Symbol, Word)

-- Lex, then parse: a lexer reads characters (`{Parse Char}`) into tokens
-- that know where they were, and a parser reads the tokens
-- (`{Parse (Parse.Located token)}`) with the same combinators. The
-- operations and combinators are generic (Parse.sw); this file is the part
-- that knows tokens come from text.

--| A value with where it was read: `offset` characters from the start of
--| the input, `length` characters long. The line and column aren't kept;
--| a message works them out from the source when it needs them.
type Parse.Located (a: Type) = { value: a, offset: Nat, length: Nat }

--| `parser`'s value with where it was read, for a lexer's tokens:
--|
--|   Parse.located (() => Num Parse.nat())
def Parse.located (parser: () → {Parse Char} a): {Parse Char} Parse.Located a :=
  let start := Parse.mark()
  let value := parser()
  let finish := Parse.mark()
  { value, offset = start.offset, length = finish.offset - start.offset }

--| `lexeme`'s values with where each was read, from where each round starts
--| for as long as characters are left; `found` is newest first.
def Parse.locatedToEndFrom (fuel: Nat) (lexeme: List Char → {Parse Char} a)
    (found: List (Parse.Located a)) (start: Parse.Mark Char):
    {Parse Char} List (Parse.Located a) :=
  match fuel, start.rest with
    | Succ more, [_, .._] => Parse.locatedToEndRound more lexeme found start (lexeme start.rest) Parse.mark()
    | _, _ =>
      Parse.note (Expected "a token")
      found.reverse

--| What `locatedToEndFrom` does with the `value` of the lexeme read from
--| `start` to `finish`, with `more` rounds left after it: on from `finish`
--| with the lexeme and where it was read, if it read something.
-- A function of its own so that proofs (Parse/RunsTokens.sw) can name it.
def Parse.locatedToEndRound (more: Nat) (lexeme: List Char → {Parse Char} a) (found: List (Parse.Located a))
    (start: Parse.Mark Char) (value: a) (finish: Parse.Mark Char):
    {Parse Char} List (Parse.Located a) :=
  if finish.offset > start.offset then
    Parse.locatedToEndFrom more lexeme
      [{ value, offset = start.offset, length = finish.offset - start.offset }, ..found]
      finish
  else Empty.absurd (Parse.fatal "`locatedToEnd`: the lexeme matched without reading anything")

--| A lexer for `Parse.tokens` whose every character belongs to a lexeme:
--| the whole input as the values of `lexeme`, each with where it was read.
--| `lexeme` is given the characters left, to choose by what comes next. It is
--| `Parse.many (() => Parse.located …)` for a lexeme that doesn't fail
--| part-way (one that does fails the whole lex, not just ends the list): with no
--| handler per lexeme and one mark, not three, it costs about a third less
--| (the toy formatter's lexer, 930 KB: 1.5 s with `many`, 0.97 s with this, native). At the end it
--| notes "expected a token", as `many` does when its last try finds nothing.
--|
--|   Parse.locatedToEnd lexemeAt
def Parse.locatedToEnd (lexeme: List Char → {Parse Char} a): {Parse Char} List (Parse.Located a) :=
  let start := Parse.mark()
  Parse.locatedToEndFrom (start.left + 1) lexeme [] start

--| Where a failure at token `index` is, in the source: the start of that
--| token, or the end of the last one when `index` is past them all.
def Parse.tokenPosition (tokens: List (Parse.Located token)) (index: Nat): Nat := match tokens.drop index with
  | [token, ..more] => token.offset
  | [] =>
    match tokens.last with
      | Some token => token.offset + token.length
      | None => 0

--| Token `index` as its author wrote it, for "got 'x'": the source's
--| characters under it, "a line break" for one, "the end of the input" past
--| the last.
def Parse.tokenFound (chars: List Char) (tokens: List (Parse.Located token)) (index: Nat): Text :=
  match tokens.drop index with
    | [] => "the end of the input"
    | [token, ..more] =>
      let written := chars.drop token.offset |> .take token.length |> Text.fromList
      if written == "\n" ∨ written == "\r\n" then "a line break" else "'${written}'"

--| `failure` of a token parser as one message, as `Parse.allMessage` makes
--| one of a character parser's: "line 3, column 9: expected ',' or ')', got
--| ';'". `chars` is the source and `tokens` what was lexed from it; the
--| failure's offset counts tokens.
def Parse.tokensMessage (chars: List Char) (tokens: List (Parse.Located token)) (failure: Parse.Failure): Text :=
  let (line, column) := Parse.lineAndColumn chars (Parse.tokenPosition tokens failure.offset)
  let expectations := failure.expectations "the end of the input"
  let expectedPart :=
    if expectations == [] then []
    else ["expected ${Parse.joinOr expectations}, got ${Parse.tokenFound chars tokens failure.offset}"]
  let described := match failure.messages ++ expectedPart with
    | [] => "the parser failed"
    | [only] => only
    | parts => Text.joinWith parts "; "
  "line ${line}, column ${column}: ${described}"

--| `Parse.tokens` for a lexer that hands back something besides its tokens,
--| and a parser that takes it: the comments after the last token, which no
--| token follows to carry them, or all the input's comments when there are no
--| tokens at all. The lexer's value is the tokens and that `extra`; the
--| parser is given `extra` and reads the tokens. Failures read as
--| `Parse.tokens`'s.
--|
--|   def parse (input: Text): {Fail} File :=
--|     Parse.tokensWith input (() => lexWithTrailer input) (trailer => file trailer)
def Parse.tokensWith (input: Text)
    (lexer: () → {Parse Char} (List (Parse.Located token), extra)) (parser: extra → {Parse (Parse.Located token)} a):
    {Fail} a :=
  let (tokens, extra) := Parse.all input lexer
  match Parse.whole tokens (() => parser extra) with
    | Ok value => value
    | Err failure => Fail.fail (Parse.tokensMessage input.toList tokens failure)

--| Lexes all of `input` with `lexer` (line breaks at the end are allowed, as
--| for `Parse.all`), then parses all of the tokens with `parser`. A lexing
--| failure reads as `Parse.all`'s. A parsing failure names the line and
--| column of the failing token, what was expected, and the token as it was
--| written: "line 3, column 9: expected ',' or ')', got ';'", or "got the
--| end of the input" past the last token. For a lexer that has more to give
--| than tokens, [`Parse.tokensWith`].
--|
--|   def parse (input: Text): {Fail} Program := Parse.tokens input (() => Parse.many token) program
def Parse.tokens (input: Text)
    (lexer: () → {Parse Char} List (Parse.Located token)) (parser: () → {Parse (Parse.Located token)} a):
    {Fail} a :=
  let tokens := Parse.all input lexer
  match Parse.whole tokens parser with
    | Ok value => value
    | Err failure => Fail.fail (Parse.tokensMessage input.toList tokens failure)

-- Tests. A small language of names, numbers and the symbols `(`, `)`, `,`
-- and `;`: lexed with positions, then read as calls `name(arg, …)`.

type Parse.Tests.Tok =
  | Word (text: Text)
  | Number (value: Nat)
  | Symbol (char: Char)

def Parse.Tests.lexToken(): {Parse Char} Parse.Located Parse.Tests.Tok :=
  Parse.span (char => char == ' ' ∨ char == '\n')
  Parse.located (() =>
    Parse.oneOf [
      () => Word (Parse.takeWhile1 "a name" Char.isAsciiLetter),
      () => Number Parse.nat(),
      () => Symbol (Parse.satisfy "a symbol" (char => char == '(' ∨ char == ')' ∨ char == ',' ∨ char == ';'))
    ])

def Parse.Tests.lex(): {Parse Char} List (Parse.Located Parse.Tests.Tok) := Parse.many Parse.Tests.lexToken

def Parse.Tests.wordOf (token: Parse.Located Parse.Tests.Tok): Option Text := match token with
  | { value = Word text, .. } => Some text
  | _ => None

def Parse.Tests.numberOf (token: Parse.Located Parse.Tests.Tok): Option Nat := match token with
  | { value = Number value, .. } => Some value
  | _ => None

def Parse.Tests.symbolIs (expected: Char) (token: Parse.Located Parse.Tests.Tok): Option () := match token with
  | { value = Symbol char, .. } => if char == expected then Some () else None
  | _ => None

def Parse.Tests.symbol (expected: Char): {Parse (Parse.Located Parse.Tests.Tok)} () :=
  Parse.one "'${expected}'" (Parse.Tests.symbolIs expected)

--| `name(1, 2)`: the name and the sum of the numbers.
def Parse.Tests.call(): {Parse (Parse.Located Parse.Tests.Tok)} (Text, Nat) :=
  let name := Parse.one "a name" Parse.Tests.wordOf
  Parse.Tests.symbol '('
  let arguments := Parse.sepBy (() => Parse.one "a number" Parse.Tests.numberOf) (() => Parse.Tests.symbol ',')
  Parse.Tests.symbol ')'
  (name, arguments.foldLeft 0 (total argument => total + argument))

def Parse.Tests.calls(): {Parse (Parse.Located Parse.Tests.Tok)} List (Text, Nat) := Parse.many (() =>
  let found := Parse.Tests.call()
  Parse.Tests.symbol ';'
  found)

def Parse.Tests.parseCalls (input: Text): Result (List (Text, Nat)) Text :=
  Fail.toResult (() => Parse.tokens input Parse.Tests.lex Parse.Tests.calls)

test "Parse.located: offset and length" :=
  match Parse.run "ab 12".toList (() => (Parse.Tests.lexToken(), Parse.Tests.lexToken())) with
    | Ok (first, second) => first.offset == 0 ∧ first.length == 2 ∧ second.offset == 3 ∧ second.length == 2
    | Err failure => False

test "Parse.one: a number among tokens" :=
  match Parse.run [{ value = Number 4, offset = 0, length = 1 }] (() => Parse.one "a number" Parse.Tests.numberOf) with
    | Ok value => value == 4
    | Err failure => False

test "Parse.one: wrong kind" :=
  match Parse.run [{ value = Word "x", offset = 0, length = 1 }] (() => Parse.one "a number" Parse.Tests.numberOf) with
    | Ok value => False
    | Err failure => failure.expected == ["a number"] ∧ failure.offset == 0

test "Parse.span1: a run of numbers" :=
  match Parse.run [1, 2, 3, 0, 5] (() => Parse.span1 "a small number" (number => number < 4)) with
    | Ok run => run.toList == [1, 2, 3, 0]
    | Err failure => False

test "Parse.span1: nothing to take" :=
  match Parse.run [5, 6] (() => Parse.span1 "a small number" (number => number < 4)) with
    | Ok run => False
    | Err failure => failure.expected == ["a small number"]

test "Parse.tokens: two calls" := Parse.Tests.parseCalls "f(1, 2); gg(3);" == Ok [("f", 3), ("gg", 3)]

test "Parse.tokens: empty input" := Parse.Tests.parseCalls "" == Ok []

test "Parse.tokens: a final line break" := Parse.Tests.parseCalls "f(1);\n" == Ok [("f", 1)]

test "Parse.tokens: a token that isn't expected, as written" :=
  Parse.Tests.parseCalls "f(1; 2)" == Err "line 1, column 4: expected ',' or ')', got ';'"

test "Parse.tokens: past the last token" :=
  Parse.Tests.parseCalls "f(1, 2" == Err "line 1, column 7: expected ',' or ')', got the end of the input"

test "Parse.tokens: a stray token at the end" :=
  Parse.Tests.parseCalls "f(1); 7" == Err "line 1, column 7: expected a name or the end of the input, got '7'"

test "Parse.tokens: the line is the token's, not the end's" :=
  Parse.Tests.parseCalls "f(1);\ng(;" == Err "line 2, column 3: expected a number or ')', got ';'"

test "Parse.tokens: a lexing failure keeps Parse.all's message" :=
  Parse.Tests.parseCalls "f(1) $" == Err "line 1, column 6: expected a name, a number or a symbol, got '$'"

-- `locatedToEnd`: a lexer of runs of spaces and runs of other characters.

def Parse.Tests.runAt (rest: List Char): {Parse Char} Text := match rest with
  | [' ', .._] => Text.fromList (Parse.span (char => char == ' '))
  | [_, .._] => Text.fromList (Parse.span (char => char != ' '))
  | [] => Parse.expected "a token"

test "Parse.locatedToEnd: every lexeme with where it was read" :=
  match Parse.run "ab  c".toList (() => Parse.locatedToEnd Parse.Tests.runAt) with
    | Ok found =>
      found
        == [
          { value = "ab", offset = 0, length = 2 },
          { value = "  ", offset = 2, length = 2 },
          { value = "c", offset = 4, length = 1 }
        ]
    | Err failure => False

test "Parse.locatedToEnd: no input" := match Parse.run ([]: List Char) (() => Parse.locatedToEnd Parse.Tests.runAt) with
  | Ok found => found == []
  | Err failure => False

test "Parse.locatedToEnd: what Parse.many of Parse.located gives" :=
  Parse.run "ab  c d".toList (() => Parse.locatedToEnd Parse.Tests.runAt)
    == Parse.run "ab  c d".toList (() => Parse.many (() => Parse.located (() => Parse.Tests.runAt Parse.mark().rest)))

test "Parse.locatedToEnd: the same message as many at the end" :=
  Parse.run "ab c".toList (() =>
    let found := Parse.locatedToEnd Parse.Tests.runAt
    Parse.satisfy "a closer" (char => char == ')')
    found)
    == Parse.run "ab c".toList (() =>
      let found := Parse.many (() => Parse.located (() => Parse.Tests.runAt Parse.mark().rest))
      Parse.satisfy "a closer" (char => char == ')')
      found)

test "Parse.locatedToEnd: a lexeme that reads nothing" :=
  match Parse.run "ab".toList (() => Parse.locatedToEnd (rest => "")) with
    | Ok found => False
    | Err failure => failure.messages == ["`locatedToEnd`: the lexeme matched without reading anything"]

-- `tokensWith`: the same lexer, then a `#` comment to the end of the input
-- that no token carries, handed to the parser.

def Parse.Tests.lexWithComment(): {Parse Char} (List (Parse.Located Parse.Tests.Tok), Option Text) :=
  let tokens := Parse.Tests.lex()
  Parse.span (char => char == ' ')
  let comment := Parse.optional (() =>
    Parse.char '#'
    Parse.span (char => char != '\n'))
  (tokens, comment.map (chars => Text.fromList chars |> .trim))

def Parse.Tests.parseWithComment (input: Text): Result (List (Text, Nat), Option Text) Text := Fail.toResult (() =>
  Parse.tokensWith input Parse.Tests.lexWithComment (comment =>
    let found := Parse.Tests.calls()
    (found, comment)))

test "Parse.tokensWith: the lexer's extra value reaches the parser" :=
  Parse.Tests.parseWithComment "f(1, 2); # done" == Ok ([("f", 3)], Some "done")

test "Parse.tokensWith: no extra value" := Parse.Tests.parseWithComment "f(1);" == Ok ([("f", 1)], None)

test "Parse.tokensWith: only the extra value, no tokens" :=
  Parse.Tests.parseWithComment "# alone" == Ok ([], Some "alone")

test "Parse.tokensWith: parsing failures read as Parse.tokens's" :=
  Parse.Tests.parseWithComment "f(1; 2) # x" == Err "line 1, column 4: expected ',' or ')', got ';'"

test "Parse.tokensWith: past the last token" :=
  Parse.Tests.parseWithComment "f(1, 2 # x" == Err "line 1, column 7: expected ',' or ')', got the end of the input"
