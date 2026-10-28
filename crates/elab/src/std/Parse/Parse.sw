import Parse.Problem (Expected, Message)

-- `Parse`: read text into the program's own types. A parser is ordinary
-- direct-style code that uses the `Parse` ability, `() → {Parse} a`, as in
-- Unison's parser libraries; a runner (`Parse.all`, `Parse.eachLine`,
-- `Parse.line`) gives it the input.
--
--   import Std.Parse (char, nat)
--
--   type Point = { x: Nat, y: Nat }
--
--   def point(): {Parse} Point :=
--     let x := nat()
--     char ','
--     let y := nat()
--     { x, y }
--
--   def parsePoints (input: Text): {Fail} (List Point) := Parse.eachLine input point
--
-- A bad line fails with "line 3, column 4: expected ','".
--
-- Choice always backs up: when an alternative of `oneOf`, `optional` or
-- `many` fails, the input is as it was before it. Errors name the furthest
-- point any alternative reached and everything expected there. A loop or
-- a recursive grammar that would run forever without reading stops the
-- whole parse with a message naming the combinator.

-- Where a parse is: the characters left, how many were read before them,
-- and how many there are.
type Parse.Mark = { rest: List Char, offset: Nat, left: Nat }

-- Why a parse failed at some point: something that was expected there, or
-- a message of the parser's own.
type Parse.Problem =
  | Expected (what: Text)
  | Message (text: Text)

-- A failed parse: what went wrong, `offset` characters in.
type Parse.Failure = { offset: Nat, message: Text }

-- The operations. Each is a token's worth of work in the handler, so a
-- parser makes a handful of them per line, not one per character.
ability Parse where
  -- The longest prefix whose characters all pass the test, read.
  span: (Char → Bool) → {Parse} (List Char)
  -- The next character, read if it passes the test.
  next: (Char → Bool) → {Parse} (Option Char)
  -- Reads the characters if they come next; whether they did.
  literal: List Char → {Parse} Bool
  -- Where the parse is.
  mark: () → {Parse} Parse.Mark
  -- Goes back to a mark.
  reset: Parse.Mark → {Parse} ()
  -- Notes a problem at the current point, for the error message.
  note: Parse.Problem → {Parse} ()
  -- Fails here; the nearest choice backs up.
  stop: () → {Parse} Empty
  -- Fails the whole parse with this message: no choice backs up. For bugs
  -- in a parser, such as a loop that would never end.
  fatal: Text → {Parse} Empty

-- What the handler keeps: where the parse is, and the furthest point a
-- problem was noted at, with the problems noted there.
type Parse.State = { at: Parse.Mark, furthest: Nat, expected: List Text, messages: List Text }

def Parse.State.add (state: Parse.State): Parse.Problem → Parse.State
  | Expected what => if state.expected.any (== what) then state else { state | expected = state.expected ++ [what] }
  | Message text => if state.messages.any (== text) then state else { state | messages = state.messages ++ [text] }

-- A problem at the current point replaces those noted nearer the start,
-- joins those noted here, and is dropped if the parse got further before.
def Parse.State.note (state: Parse.State) (problem: Parse.Problem): Parse.State :=
  if state.at.offset > state.furthest then
    Parse.State.add { state | furthest = state.at.offset, expected = [], messages = [] } problem
  else if state.at.offset == state.furthest then state.add problem
  else state

def Parse.State.advance (state: Parse.State) (rest: List Char) (count: Nat): Parse.State :=
  { state | at = { rest, offset = state.at.offset + count, left = state.at.left - count } }

-- What each reading operation gives, and the state after it. The handler
-- resumes with the two directly, so that every resumption is a tail call
-- and the parse runs in constant stack and heap per operation.
def Parse.State.span (state: Parse.State) (passes: Char → Bool): (List Char, Parse.State) :=
  let split := state.at.rest.span passes
  (split.fst, state.advance split.snd split.fst.length)

def Parse.State.next (state: Parse.State) (passes: Char → Bool): (Option Char, Parse.State) :=
  match state.at.rest with
    | Cons char after => if passes char then (Some char, state.advance after 1) else (None, state)
    | Nil => (None, state)

def Parse.State.literal (state: Parse.State) (chars: List Char): (Bool, Parse.State) :=
  match Text.stripPrefixChars chars state.at.rest with
    | Some after => (True, state.advance after chars.length)
    | None => (False, state)

-- The furthest point's problems: the parser's own messages, then
-- "expected A or B".
def Parse.State.failure (state: Parse.State): Parse.Failure :=
  let expectations := if state.expected == [] then [] else ["expected ${Text.joinWith state.expected " or "}"]
  let message :=
    match state.messages ++ expectations with
      | [] => "the parser failed"
      | [only] => only
      | parts => Text.joinWith parts "; "
  { offset = state.furthest, message }

-- Runs `parser` from `state`: its value, or where and why it failed.
def Parse.runFrom (initial: Parse.State) (parser: () → {Parse} a): Result a Parse.Failure :=
  let go: Parse.State → Result a Parse.Failure :=
    handle parser() with
      | return value => state => Ok value
      | Parse.span passes, k => state =>
        let step := state.span passes
        k step.fst step.snd
      | Parse.next passes, k => state =>
        let step := state.next passes
        k step.fst step.snd
      | Parse.literal chars, k => state =>
        let step := state.literal chars
        k step.fst step.snd
      | Parse.mark u, k => state => k state.at state
      | Parse.reset at, k => state => k () { state | at }
      | Parse.note problem, k => state => k () (state.note problem)
      | Parse.stop u, k => state => Err state.failure
      | Parse.fatal message, k => state => Err ({ offset = state.at.offset, message })
  go initial

-- The state at the start of `input`.
def Parse.State.start (input: List Char): Parse.State :=
  { at = { rest = input, offset = 0, left = input.length }, furthest = 0, expected = [], messages = [] }

-- Runs `parser` from the start of `input`: its value, or where and why it
-- failed. It needn't read all of the input.
def Parse.run (input: List Char) (parser: () → {Parse} a): Result a Parse.Failure :=
  Parse.runFrom (Parse.State.start input) parser

-- Failing. Each fails at the current point: the nearest choice backs up,
-- and if nothing gets further the message is reported here.

-- Fails with `message`, whatever result was expected.
def Parse.fail (message: Text): {Parse} a :=
  Parse.note (Message message)
  Empty.absurd Parse.stop()

-- Fails with "expected `what`"; other expectations at the same point are
-- joined to it with "or".
def Parse.expected (what: Text): {Parse} a :=
  Parse.note (Expected what)
  Empty.absurd Parse.stop()

-- Fails with `message` unless `ok`.
def Parse.ensure (ok: Bool) (message: Text): {Parse} () := if ok then () else Parse.fail message

-- The value in an `Option`, or fail with `message`.
def Parse.need (option: Option a) (message: Text): {Parse} a :=
  match option with
    | Some value => value
    | None => Parse.fail message

-- A `Fail` computation's value; its failure is a parse failure here:
-- `Parse.fromFail (() => word.toNatOrFail)`.
def Parse.fromFail (computation: () → {Fail} a): {Parse} a := Fail.recover (message => Parse.fail message) computation

-- Pieces. Each reads a token or fails with what it expected.

-- The next character if `passes` holds for it, else "expected `what`".
def Parse.satisfy (what: Text) (passes: Char → Bool): {Parse} Char :=
  match Parse.next passes with
    | Some char => char
    | None => Parse.expected what

-- The character `expected`, else "expected 'c'".
def Parse.char (expected: Char): {Parse} () :=
  let char := Parse.satisfy "'${expected}'" (== expected)
  ()

-- The text `expected`, else "expected 'text'".
def Parse.text (expected: Text): {Parse} () :=
  if Parse.literal expected.toList then () else Parse.expected "'${expected}'"

-- The longest run of characters for which `passes` holds, possibly empty. Never fails.
def Parse.takeWhile (passes: Char → Bool): {Parse} Text := Parse.span passes |> Text.fromList

-- The longest run of characters for which `passes` holds, at least one, else
-- "expected `what`".
def Parse.takeWhile1 (what: Text) (passes: Char → Bool): {Parse} Text :=
  match Parse.span passes with
    | Nil => Parse.expected what
    | chars => Text.fromList chars

def Parse.isDigit (char: Char): Bool := char.digitValue.isSome

def Parse.isSpace (char: Char): Bool := char == ' ' ∨ char == '\t'

-- A whole number written in decimal digits, else "expected a number".
def Parse.nat(): {Parse} Nat :=
  match Parse.span Parse.isDigit with
    | Nil => Parse.expected "a number"
    | digits => digits.map (digit => digit.digitValue.getOrElse 0) |> Nat.fromDigits

-- A whole number with an optional '-' in front, else "expected a number".
def Parse.int(): {Parse} Int :=
  if Parse.literal ['-'] then -(Parse.nat().toInt) else Parse.nat().toInt

-- One decimal digit, else "expected a digit".
def Parse.digit(): {Parse} (Fin 10) :=
  let char := Parse.satisfy "a digit" Parse.isDigit
  Parse.need char.toDigit "expected a digit"

-- Spaces and tabs, possibly none. Never fails.
def Parse.spaces(): {Parse} () :=
  let skipped := Parse.span Parse.isSpace
  ()

-- A line break, "\n" or "\r\n", else "expected a line break".
def Parse.newline(): {Parse} () :=
  if Parse.literal ['\n'] then () else if Parse.literal ['\r', '\n'] then () else Parse.expected "a line break"

-- Two line breaks in a row, else "expected a blank line".
def Parse.blankLine(): {Parse} () :=
  Parse.label "a blank line" (() =>
    Parse.newline()
    Parse.newline())

-- The end of the input, else "expected the end".
def Parse.end(): {Parse} () := if Parse.mark().left == 0 then () else Parse.expected "the end"

-- The value paired with the first word that comes next, as aoc-parse's
-- `{ "L" => …, "R" => … }`; else "expected 'L' or 'R'". Words are tried in
-- order, so put a word before any that start it.
def Parse.pick (choices: List (Text, a)): {Parse} a :=
  match choices.find (choice => Parse.literal choice.fst.toList) with
    | Some (word, value) => value
    | None => Parse.expected (choices.map (choice => "'${choice.fst}'") |> Text.joinWith " or ")

-- Choice and repetition. A failed alternative leaves the input as it was.

-- `Some` of `parser`'s value, or `None` with the input as it was if it
-- fails. Never fails.
def Parse.optional (parser: () → {Parse} a): {Parse} (Option a) :=
  let start := Parse.mark()
  handle parser() with
    | return value => Some value
    | Parse.span passes, k => k (Parse.span passes)
    | Parse.next passes, k => k (Parse.next passes)
    | Parse.literal chars, k => k (Parse.literal chars)
    | Parse.mark u, k => k Parse.mark()
    | Parse.reset at, k => k (Parse.reset at)
    | Parse.note problem, k => k (Parse.note problem)
    | Parse.stop u, k =>
      Parse.reset start
      None
    | Parse.fatal message, k => Empty.absurd (Parse.fatal message)

def Parse.oneOfFrom (first: () → {Parse} a): List (() → {Parse} a) → {Parse} a
  | [] => first()
  | [next, ..rest] =>
    match Parse.optional first with
      | Some value => value
      | None => Parse.oneOfFrom next rest

-- The value of the first alternative that succeeds; if none does, the
-- failure that got furthest.
def Parse.oneOf: List (() → {Parse} a) → {Parse} a
  | [] => Parse.fail "`oneOf`: no alternatives"
  | [first, ..rest] => Parse.oneOfFrom first rest

-- `parser` while it succeeds, at most `fuel` times. `found` is newest first.
def Parse.manyFuel (fuel: Nat) (parser: () → {Parse} a) (found: List a): {Parse} (List a) :=
  match fuel with
    | Zero => found.reverse
    | Succ more =>
      let before := Parse.mark()
      match Parse.optional parser with
        | None => found.reverse
        | Some value =>
          if Parse.mark().offset > before.offset then Parse.manyFuel more parser (Cons value found)
          else Empty.absurd (Parse.fatal "`many`: the parser matched without reading anything")

-- `parser`'s values while it succeeds, possibly none. Fails only if
-- `parser` succeeds without reading anything, which would repeat forever:
-- that stops the whole parse. Every other round reads a character, so the
-- characters left are enough fuel.
def Parse.many (parser: () → {Parse} a): {Parse} (List a) := Parse.manyFuel (Parse.mark().left + 1) parser []

-- `parser`'s values while it succeeds, at least one.
def Parse.many1 (parser: () → {Parse} a): {Parse} (List a) :=
  let first := parser()
  Cons first (Parse.many parser)

-- `parser`, then `separator` and `parser` again as long as both match: at
-- least one value.
def Parse.sepBy1 (parser: () → {Parse} a) (separator: () → {Parse} ()): {Parse} (List a) :=
  let first := parser()
  Cons first (Parse.many (() =>
    separator()
    parser()))

-- The same, possibly none. Never fails.
def Parse.sepBy (parser: () → {Parse} a) (separator: () → {Parse} ()): {Parse} (List a) :=
  Parse.optional (() => Parse.sepBy1 parser separator) |> .getOrElse []

-- One `parser` per line, at least one. The line break after the last is
-- left for what comes next.
def Parse.lines (parser: () → {Parse} a): {Parse} (List a) := Parse.sepBy1 parser Parse.newline

-- Blocks separated by a blank line, at least one: `sections (() => lines nat)`.
def Parse.sections (parser: () → {Parse} a): {Parse} (List a) := Parse.sepBy1 parser Parse.blankLine

-- Rows of cells, one row per line, at least one cell in each. Rows may
-- differ in length.
def Parse.grid (cell: () → {Parse} a): {Parse} (List (List a)) := Parse.lines (() => Parse.many1 cell)

-- `parser`'s value and whether it read anything, or `None` with the input
-- as it was if it fails: `optional` with the progress check built in.
def Parse.attempt (parser: () → {Parse} a): {Parse} (Option (a, Bool)) :=
  let start := Parse.mark()
  handle parser() with
    | return value =>
      let finish := Parse.mark()
      let progressed: Bool := finish.offset > start.offset
      Some (value, progressed)
    | Parse.span passes, k => k (Parse.span passes)
    | Parse.next passes, k => k (Parse.next passes)
    | Parse.literal chars, k => k (Parse.literal chars)
    | Parse.mark u, k => k Parse.mark()
    | Parse.reset at, k => k (Parse.reset at)
    | Parse.note problem, k => k (Parse.note problem)
    | Parse.stop u, k =>
      Parse.reset start
      None
    | Parse.fatal message, k => Empty.absurd (Parse.fatal message)

-- `findAll`'s loop, at most `fuel` rounds: `skipNoise`, then `parser`, and
-- if that didn't read anything, one character skipped. `found` is newest
-- first.
def Parse.findAllFuel (fuel: Nat) (skipNoise: () → {Parse} ()) (parser: () → {Parse} a) (found: List a): {Parse} (List a) :=
  match fuel with
    | Zero => found.reverse
    | Succ more =>
      skipNoise()
      let attempt := Parse.attempt parser
      let foundNow := attempt.map (matched => Cons matched.fst found) |> .getOrElse found
      if attempt.map (matched => matched.snd) |> .getOrElse False then Parse.findAllFuel more skipNoise parser foundNow
      else
        match Parse.next (char => True) with
          | Some skipped => Parse.findAllFuel more skipNoise parser foundNow
          | None => foundNow.reverse

-- The values of `parser` everywhere it matches in the rest of the input,
-- left to right, without overlapping, as Python's `re.findall`: where it
-- doesn't match, one character is skipped, and the next try starts there.
-- A match that reads nothing is kept, and a character is skipped after it.
-- Reads all of the input and never fails.
def Parse.findAll (parser: () → {Parse} a): {Parse} (List a) := Parse.findAllFuel (Parse.mark().left + 1) (() => ()) parser []

-- The same, for a `parser` that can match only where `starts` holds for the
-- next character: the characters between are skipped with one `span`, not
-- tried one at a time. A match starting anywhere else is missed.
def Parse.findAllStarting (starts: Char → Bool) (parser: () → {Parse} a): {Parse} (List a) :=
  let skipNoise := () =>
    let skipped := Parse.span (char => ¬(starts char))
    ()
  Parse.findAllFuel (Parse.mark().left + 1) skipNoise parser []

-- `parser`, but if it fails without getting past where it started, it
-- fails with "expected `what`" in place of what it expected there
-- (Megaparsec's `label`).
def Parse.label (what: Text) (parser: () → {Parse} a): {Parse} a :=
  let start := Parse.mark()
  handle parser() with
    | return value =>
      if Parse.mark().offset == start.offset then Parse.note (Expected what) else ()
      value
    | Parse.span passes, k => k (Parse.span passes)
    | Parse.next passes, k => k (Parse.next passes)
    | Parse.literal chars, k => k (Parse.literal chars)
    | Parse.mark u, k => k Parse.mark()
    | Parse.reset at, k => k (Parse.reset at)
    | Parse.note problem, k =>
      if Parse.mark().offset == start.offset then k () else k (Parse.note problem)
    | Parse.stop u, k =>
      Parse.reset start
      Parse.expected what
    | Parse.fatal message, k => Empty.absurd (Parse.fatal message)

-- `body` with `self` for its nested parser, at most `fuel` levels deep.
def Parse.recursiveFuel (fuel: Nat) (body: (() → {Parse} a) → {Parse} a): {Parse} a :=
  match fuel with
    | Zero => Empty.absurd (Parse.fatal "`recursive`: the parser called itself without reading anything")
    | Succ more => body (() => Parse.recursiveFuel more body)

-- A parser for nested input: `body` gets the parser being defined, to call
-- for the nested parts. Fails only as `body` does, or if it nests without
-- reading anything between levels (left recursion), which would recurse
-- forever: that stops the whole parse. Every other level reads a
-- character, so the characters left are enough fuel.
def Parse.recursive (body: (() → {Parse} a) → {Parse} a): {Parse} a :=
  Parse.recursiveFuel (Parse.mark().left + 1) body

-- Runners. The parser must read all of its input; errors give the line and
-- column, counted from 1.

-- `parser`, then the end.
def Parse.whole (chars: List Char) (parser: () → {Parse} a): Result a Parse.Failure :=
  Parse.run chars (() =>
    let value := parser()
    Parse.end()
    value)

-- The line and column of the character `offset` characters into `chars`.
def Parse.lineAndColumn (chars: List Char) (offset: Nat): (Nat, Nat) :=
  let before := chars.take offset
  let column := before.reverse.takeWhile (≠ '\n') |> .length
  (before.count (== '\n') + 1, column + 1)

-- `parser` on all of `input`, else fail with "line 3, column 5: expected
-- ','". For input with sections; holds the input as a list of characters,
-- so for large line-per-record input `Parse.eachLine` is faster and smaller.
-- A line break at the end of the input is allowed.
def Parse.all (input: Text) (parser: () → {Parse} a): {Fail} a :=
  let chars := input.toList
  let withFinalLineBreak := () =>
    let value := parser()
    let finalLineBreak := Parse.optional Parse.newline
    value
  match Parse.whole chars withFinalLineBreak with
    | Ok value => value
    | Err failure =>
      let (line, column) := Parse.lineAndColumn chars failure.offset
      Fail.fail "line ${line}, column ${column}: ${failure.message}"

-- `parser` on one line, else fail with "column 5: expected ','".
def Parse.line (line: Text) (parser: () → {Parse} a): {Fail} a :=
  match Parse.whole line.toList parser with
    | Ok value => value
    | Err failure => Fail.fail "column ${failure.offset + 1}: ${failure.message}"

-- `parser` on each line of `input`, split as `Text.lines` splits, else fail
-- with "line 3, column 5: expected ','" for the first line that fails.
-- Lines are numbered from 1, as `Aoc.Common.parseLines` numbers them.
def Parse.eachLine (input: Text) (parser: () → {Parse} a): {Fail} (List a) :=
  input.lines.withIndex.map (((index, line)) =>
    match Parse.whole line.toList parser with
      | Ok value => value
      | Err failure => Fail.fail "line ${index + 1}, column ${failure.offset + 1}: ${failure.message}")

-- What the handler does with each operation followed by the rest of the
-- parser `k`. Each holds by `rfl`, or one `rewrite`.

theorem Parse.runFromPure (state: Parse.State) (value: a): Parse.runFrom state (() => value) = Ok value := rfl

theorem Parse.runFromMark (state: Parse.State) (k: Parse.Mark → {Parse} a):
    Parse.runFrom state (() => k Parse.mark()) = Parse.runFrom state (() => k state.at) := rfl

theorem Parse.runFromReset (state: Parse.State) (at: Parse.Mark) (k: () → {Parse} a):
    Parse.runFrom state (() => k (Parse.reset at)) = Parse.runFrom { state | at } (() => k ()) := rfl

theorem Parse.runFromNote (state: Parse.State) (problem: Parse.Problem) (k: () → {Parse} a):
    Parse.runFrom state (() => k (Parse.note problem)) = Parse.runFrom (state.note problem) (() => k ()) := rfl

theorem Parse.runFromStop (state: Parse.State) (k: Empty → {Parse} a):
    Parse.runFrom state (() => k Parse.stop()) = Err state.failure := rfl

theorem Parse.runFromFatal (state: Parse.State) (message: Text) (k: Empty → {Parse} a):
    Parse.runFrom state (() => k (Parse.fatal message)) = Err ({ offset = state.at.offset, message }) := rfl

theorem Parse.runFromSpan (state: Parse.State) (passes: Char → Bool) (k: List Char → {Parse} a):
    Parse.runFrom state (() => k (Parse.span passes)) =
      Parse.runFrom (state.advance (state.at.rest.span passes).snd (state.at.rest.span passes).fst.length) (() => k (state.at.rest.span passes).fst) :=
  rfl

-- `literal` where the input starts with the characters: it reads them.
theorem Parse.runFromLiteralThere (state: Parse.State) (chars: List Char) (rest: List Char) (k: Bool → {Parse} a)
    (starts: state.at.rest = List.append chars rest):
    Parse.runFrom state (() => k (Parse.literal chars)) = Parse.runFrom (state.advance rest chars.length) (() => k True) :=
  rewrite starts, Text.stripPrefixCharsAppend rest chars

theorem Parse.runPure (input: List Char) (value: a): Parse.run input (() => value) = Ok value := rfl

theorem Parse.runFail (message: Text): Parse.run [] (() => (Parse.fail message: Nat)) = Err ({ offset = 0, message }) := rfl

-- Tests. Each runs a parser with `Parse.line` (errors give the column) or
-- `Parse.all` (the line and column).

def Parse.Tests.lineResult (line: Text) (parser: () → {Parse} a): Result a Text := Fail.toResult (() => Parse.line line parser)

def Parse.Tests.allResult (input: Text) (parser: () → {Parse} a): Result a Text := Fail.toResult (() => Parse.all input parser)

-- The error if `parser` fails on `line`, else "": for parsers whose value is `()`.
def Parse.Tests.lineError (line: Text) (parser: () → {Parse} a): Text := Parse.Tests.lineResult line parser |> .errorOrElse ""

test "Parse: char" := Parse.Tests.lineError "a" (() => Parse.char 'a') == ""
test "Parse: char, error" := Parse.Tests.lineError "b" (() => Parse.char 'a') == "column 1: expected 'a'"
test "Parse: text" := Parse.Tests.lineResult "p=4" (() =>
  Parse.text "p="
  Parse.nat()) == Ok 4
test "Parse: text, error" := Parse.Tests.lineError "p-4" (() => Parse.text "p=") == "column 1: expected 'p='"
test "Parse: satisfy" := Parse.Tests.lineResult "e" (() => Parse.satisfy "a vowel" (char => "aeiou".toList.any (== char))) == Ok 'e'
test "Parse: satisfy, error" :=
  Parse.Tests.lineResult "x" (() => Parse.satisfy "a vowel" (char => "aeiou".toList.any (== char))) == Err "column 1: expected a vowel"
test "Parse: takeWhile" := Parse.Tests.lineResult "aab" (() =>
  let run := Parse.takeWhile (== 'a')
  Parse.char 'b'
  run) == Ok "aa"
test "Parse: takeWhile, none" := Parse.Tests.lineResult "" (() => Parse.takeWhile (== 'a')) == Ok ""
test "Parse: takeWhile1" := Parse.Tests.lineResult "aa" (() => Parse.takeWhile1 "an a" (== 'a')) == Ok "aa"
test "Parse: takeWhile1, error" := Parse.Tests.lineResult "b" (() => Parse.takeWhile1 "an a" (== 'a')) == Err "column 1: expected an a"
test "Parse: nat" := Parse.Tests.lineResult "1203" Parse.nat == Ok 1203
test "Parse: nat, error" := Parse.Tests.lineResult "x" Parse.nat == Err "column 1: expected a number"
test "Parse: nat, then the end" := Parse.Tests.lineResult "12x" Parse.nat == Err "column 3: expected the end"
test "Parse: int" := Parse.Tests.lineResult "-12" Parse.int == Ok (-12)
test "Parse: int, positive" := Parse.Tests.lineResult "12" Parse.int == Ok 12
test "Parse: int, error" := Parse.Tests.lineResult "-" Parse.int == Err "column 2: expected a number"
test "Parse: digit" := Parse.Tests.lineResult "7" (() => Parse.digit().toNat) == Ok 7
test "Parse: digit, error" := Parse.Tests.lineResult "x" (() => Parse.digit().toNat) == Err "column 1: expected a digit"
test "Parse: spaces" := Parse.Tests.lineResult " \t 5" (() =>
  Parse.spaces()
  Parse.nat()) == Ok 5
test "Parse: newline" := Parse.Tests.lineResult "1\n2" (() => Parse.sepBy1 Parse.nat Parse.newline) == Ok [1, 2]
test "Parse: newline, CRLF" := Parse.Tests.lineResult "1\r\n2" (() => Parse.sepBy1 Parse.nat Parse.newline) == Ok [1, 2]
test "Parse: newline, error" := Parse.Tests.lineError "x" Parse.newline == "column 1: expected a line break"
test "Parse: blankLine" := Parse.Tests.lineError "\n\n" Parse.blankLine == ""
test "Parse: blankLine, error" := Parse.Tests.lineError "x" Parse.blankLine == "column 1: expected a blank line"
test "Parse: end" := Parse.Tests.lineError "" Parse.end == ""
test "Parse: pick" := Parse.Tests.lineResult "R" (() => Parse.pick [("L", 1), ("R", 2)]) == Ok 2
test "Parse: pick, error" := Parse.Tests.lineResult "X" (() => Parse.pick [("L", 1), ("R", 2)]) == Err "column 1: expected 'L' or 'R'"
test "Parse: pick, first word first" := Parse.Tests.lineResult "<=" (() => Parse.pick [("<=", 0), ("<", 1)]) == Ok 0

test "Parse: optional" := Parse.Tests.lineResult "+5" (() =>
  let sign := Parse.optional (() => Parse.char '+')
  (sign.isSome, Parse.nat())) == Ok (True, 5)
test "Parse: optional, absent" := Parse.Tests.lineResult "5" (() =>
  let sign := Parse.optional (() => Parse.char '+')
  (sign.isSome, Parse.nat())) == Ok (False, 5)
-- A failed alternative leaves the input as it was, even after reading.
test "Parse: optional backs up" := Parse.Tests.lineResult "abd" (() =>
  let partial := Parse.optional (() =>
    Parse.char 'a'
    Parse.char 'b'
    Parse.char 'c')
  Parse.text "abd"
  partial.isSome) == Ok False
test "Parse: oneOf" := Parse.Tests.lineResult "ac" (() =>
  Parse.oneOf [
    () =>
      Parse.text "ab"
      1,
    () =>
      Parse.text "ac"
      2
  ]) == Ok 2
-- The error is from the furthest point, with everything expected there.
test "Parse: oneOf, error" := Parse.Tests.lineError "ad" (() =>
  Parse.oneOf [
    () =>
      Parse.char 'a'
      Parse.char 'b',
    () =>
      Parse.char 'a'
      Parse.char 'c'
  ]) == "column 2: expected 'b' or 'c'"
test "Parse: oneOf, none" := Parse.Tests.lineResult "a" (() => (Parse.oneOf []: Nat)) == Err "column 1: `oneOf`: no alternatives"
test "Parse: many" := Parse.Tests.lineResult "aaab" (() =>
  let found := Parse.many (() => Parse.satisfy "an a" (== 'a'))
  Parse.char 'b'
  found) == Ok ['a', 'a', 'a']
test "Parse: many, none" := Parse.Tests.lineResult "" (() => Parse.many Parse.nat) == Ok []
test "Parse: many, reading nothing" :=
  Parse.Tests.lineError "ab" (() => Parse.many Parse.spaces) == "column 1: `many`: the parser matched without reading anything"
-- No choice backs out of that failure.
test "Parse: many, reading nothing, inside optional" :=
  Parse.Tests.lineError "ab" (() => Parse.optional (() => Parse.many Parse.spaces)) ==
    "column 1: `many`: the parser matched without reading anything"
test "Parse: many1" := Parse.Tests.lineResult "aa" (() => Parse.many1 (() => Parse.satisfy "an a" (== 'a'))) == Ok ['a', 'a']
test "Parse: many1, error" := Parse.Tests.lineResult "" (() => Parse.many1 (() => Parse.satisfy "an a" (== 'a'))) == Err "column 1: expected an a"
test "Parse: sepBy" := Parse.Tests.lineResult "1,2,3" (() => Parse.sepBy Parse.nat (() => Parse.char ',')) == Ok [1, 2, 3]
test "Parse: sepBy, none" := Parse.Tests.lineResult "" (() => Parse.sepBy Parse.nat (() => Parse.char ',')) == Ok []
test "Parse: sepBy1, error" := Parse.Tests.lineResult "1,2," (() => Parse.sepBy1 Parse.nat (() => Parse.char ',')) == Err "column 5: expected a number"
test "Parse: lines" := Parse.Tests.allResult "1\n2\n" (() => Parse.lines Parse.nat) == Ok [1, 2]
test "Parse: lines, error" := Parse.Tests.allResult "1\n2\nx\n" (() => Parse.lines Parse.nat) == Err "line 3, column 1: expected a number or the end"
test "Parse: sections" := Parse.Tests.allResult "1\n2\n\n3\n" (() => Parse.sections (() => Parse.lines Parse.nat)) == Ok [[1, 2], [3]]
test "Parse: grid" :=
  Parse.Tests.allResult "@.\n.@\n" (() => Parse.grid (() => Parse.pick [("@", True), (".", False)])) == Ok [[True, False], [False, True]]
test "Parse: grid, error" :=
  Parse.Tests.allResult "@.\n.x\n" (() => Parse.grid (() => Parse.pick [("@", True), (".", False)])) ==
    Err "line 2, column 2: expected '@' or '.' or a line break or the end"
test "Parse: label" :=
  Parse.Tests.lineResult "X5" (() => Parse.label "a turn like L68" (() => Parse.pick [("L", 1), ("R", 2)])) ==
    Err "column 1: expected a turn like L68"
-- A labelled parser that got further reports what it expected there.
test "Parse: label, further in" := Parse.Tests.lineResult "1,x" (() =>
  Parse.label "a pair like 1,2" (() =>
    let left := Parse.nat()
    Parse.char ','
    (left, Parse.nat()))) == Err "column 3: expected a number"

-- Nested lists of numbers, summed: "[1,[2,[]],3]".
def Parse.Tests.nestedSum(): {Parse} Nat :=
  Parse.recursive (nested =>
    Parse.oneOf [
      Parse.nat,
      () =>
        Parse.char '['
        let items := Parse.sepBy nested (() => Parse.char ',')
        Parse.char ']'
        items.sum
    ])

test "Parse: recursive" := Parse.Tests.lineResult "[1,[2,[]],3]" Parse.Tests.nestedSum == Ok 6
test "Parse: recursive, error" :=
  Parse.Tests.lineResult "[1,[2,x]]" Parse.Tests.nestedSum == Err "column 7: expected a number or '['"
test "Parse: recursive, left recursion" := Parse.Tests.lineResult "1+2" (() =>
  Parse.recursive (self =>
    let left := self()
    Parse.char '+'
    left + Parse.nat())) ==
  Err "column 1: `recursive`: the parser called itself without reading anything"

test "Parse: fail" := Parse.Tests.lineResult "a" (() => (Parse.fail "no": Nat)) == Err "column 1: no"
test "Parse: expected" := Parse.Tests.lineResult "a" (() => (Parse.expected "a b": Nat)) == Err "column 1: expected a b"
-- A message and an expectation at the same point are both reported.
test "Parse: fail beside expected" := Parse.Tests.lineError "y" (() =>
  Parse.oneOf [
    () => Parse.fail "not this",
    () => Parse.char 'x'
  ]) == "column 1: not this; expected 'x'"
test "Parse: ensure" := Parse.Tests.lineResult "5" (() =>
  let number := Parse.nat()
  Parse.ensure (number > 9) "too small"
  number) == Err "column 2: too small"
test "Parse: need" := Parse.Tests.lineResult "" (() => Parse.need (None: Option Nat) "nothing") == Err "column 1: nothing"
test "Parse: fromFail" := Parse.Tests.lineResult "ab" (() =>
  let word := Parse.takeWhile (char => char ≠ ' ')
  Parse.fromFail (() => word.toNatOrFail)) == Err "column 3: expected a whole number, got 'ab'"
test "Parse: fromFail, success" := Parse.Tests.lineResult "12" (() =>
  let word := Parse.takeWhile (char => char ≠ ' ')
  Parse.fromFail (() => word.toNatOrFail)) == Ok 12

test "Parse: all" :=
  Parse.Tests.allResult "1,2\n3,4" (() => Parse.lines (() => Parse.sepBy1 Parse.nat (() => Parse.char ','))) == Ok [[1, 2], [3, 4]]
test "Parse: all, error" :=
  Parse.Tests.allResult "1,2\n3;4\n" (() => Parse.lines (() => Parse.sepBy1 Parse.nat (() => Parse.char ','))) ==
    Err "line 2, column 2: expected ',' or a line break or the end"
test "Parse: all, one line" :=
  Parse.Tests.allResult "1,2x" (() => Parse.sepBy1 Parse.nat (() => Parse.char ',')) == Err "line 1, column 4: expected ',' or a line break or the end"
test "Parse: eachLine" :=
  Fail.toResult (() => Parse.eachLine "1,2\n3,4\n" (() => Parse.sepBy1 Parse.nat (() => Parse.char ','))) == Ok [[1, 2], [3, 4]]
test "Parse: eachLine, error" :=
  Fail.toResult (() => Parse.eachLine "1,2\n3x4" (() => Parse.sepBy1 Parse.nat (() => Parse.char ','))) ==
    Err "line 2, column 2: expected ',' or the end"
test "Parse: eachLine, empty" := Fail.toResult (() => Parse.eachLine "" Parse.nat) == Ok []
-- A failure keeps its line under `Fail.context`, as `Aoc.Common.parseLines` does.
test "Parse: eachLine, in context" :=
  Fail.toResult (() => Fail.context "input" (() => Parse.eachLine "x" Parse.nat)) == Err "input: line 1, column 1: expected a number"
