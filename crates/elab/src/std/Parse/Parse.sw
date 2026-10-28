import Parse.Problem (Expected, Literal, Message)

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
-- A bad line fails with "line 3, column 4: expected ',', got ';'".
--
-- Choice always backs up: when an alternative of `oneOf`, `optional` or
-- `many` fails, the input is as it was before it. Errors name the furthest
-- point any alternative reached, everything expected there, and what was
-- found there instead. A loop or
-- a recursive grammar that would run forever without reading stops the
-- whole parse with a message naming the combinator.

-- Where a parse is: the characters left, how many were read before them,
-- and how many there are.
type Parse.Mark = { rest: List Char, offset: Nat, left: Nat }

-- Why a parse failed at some point: something that was expected there, a
-- text that was expected there, or a message of the parser's own.
type Parse.Problem =
  | Expected (what: Text)
  | Literal (text: Text)
  | Message (text: Text)

-- A failed parse, `offset` characters in: the parser's own messages and
-- what was expected there. A runner makes one message of it with
-- `Parse.Failure.describe`.
type Parse.Failure = { offset: Nat, messages: List Text, expected: List Text, width: Nat }

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
-- problem was noted at, with the problems noted there and the length of
-- the longest text expected there (how much of the input to show as what
-- was found).
type Parse.State = { at: Parse.Mark, furthest: Nat, expected: List Text, messages: List Text, width: Nat }

def Parse.State.expect (state: Parse.State) (what: Text): Parse.State :=
  if state.expected.any (== what) then state else { state | expected = state.expected ++ [what] }

def Parse.State.add (state: Parse.State): Parse.Problem → Parse.State
  | Expected what => state.expect what
  | Literal text => { state.expect "'${text}'" | width = Nat.max state.width text.length }
  | Message text => if state.messages.any (== text) then state else { state | messages = state.messages ++ [text] }

-- A problem at the current point replaces those noted nearer the start,
-- joins those noted here, and is dropped if the parse got further before.
-- What was expected here before a message is from attempts that didn't
-- fail the parse, such as the digit `many digit` tried after the last one,
-- so a message replaces it, as Megaparsec's `fail` drops its hints.
def Parse.State.note (state: Parse.State) (problem: Parse.Problem): Parse.State :=
  if state.at.offset > state.furthest then
    Parse.State.add { state | furthest = state.at.offset, expected = [], messages = [], width = 0 } problem
  else if state.at.offset == state.furthest then
    match problem with
      | Message text => Parse.State.add { state | expected = [], width = 0 } problem
      | _ => state.add problem
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

-- The furthest point and its problems.
def Parse.State.failure (state: Parse.State): Parse.Failure :=
  { offset = state.furthest, messages = state.messages, expected = state.expected, width = state.width }

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
      | Parse.fatal message, k => state => Err ({ offset = state.at.offset, messages = [message], expected = [], width = 0 })
  go initial

-- The state at the start of `input`.
def Parse.State.start (input: List Char): Parse.State :=
  { at = { rest = input, offset = 0, left = input.length }, furthest = 0, expected = [], messages = [], width = 0 }

-- Runs `parser` from the start of `input`: its value, or where and why it
-- failed. It needn't read all of the input.
def Parse.run (input: List Char) (parser: () → {Parse} a): Result a Parse.Failure :=
  Parse.runFrom (Parse.State.start input) parser

-- Failing. Each fails at the current point: the nearest choice backs up,
-- and if nothing gets further the message is reported here.

-- Fails with `message`, whatever result was expected. It replaces what
-- attempts that didn't fail the parse expected here: `ensure` after `many1
-- digit` gives its own message, without "or a digit".
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

-- Fails with `message` unless `ok`, reported at `at` rather than here: for a
-- check on something read since `at`, such as a number's size.
def Parse.ensureAt (at: Parse.Mark) (ok: Bool) (message: Text): {Parse} () :=
  if ok then ()
  else
    Parse.reset at
    Parse.fail message

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
  if Parse.literal expected.toList then ()
  else
    Parse.note (Literal expected)
    Empty.absurd Parse.stop()

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

-- A whole number of `atLeast` to `atMost` decimal digits (at least one),
-- else "expected a number of 1 to 3 digits" where the number starts. All
-- the digits there are read first, so "1234" is too long, not 123 and a 4.
def Parse.natDigits (atLeast: Nat) (atMost: Nat): {Parse} Nat :=
  let start := Parse.mark()
  let digits := Parse.span Parse.isDigit
  let count := digits.length
  if 0 < count ∧ atLeast ≤ count ∧ count ≤ atMost then digits.map (digit => digit.digitValue.getOrElse 0) |> Nat.fromDigits
  else
    Parse.reset start
    Parse.expected (if atLeast == atMost then "a number of ${atLeast} digits" else "a number of ${atLeast} to ${atMost} digits")

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

-- Spaces and tabs, at least one, else "expected a space".
def Parse.spaces1(): {Parse} () :=
  let skipped := Parse.takeWhile1 "a space" Parse.isSpace
  ()

-- `parser` with spaces and tabs allowed around it: `token nat` reads " 12 ".
def Parse.token (parser: () → {Parse} a): {Parse} a :=
  Parse.spaces()
  let value := parser()
  Parse.spaces()
  value

-- A line break, "\n" or "\r\n", else "expected a line break".
def Parse.newline(): {Parse} () :=
  if Parse.literal ['\n'] then () else if Parse.literal ['\r', '\n'] then () else Parse.expected "a line break"

-- A line break or the end of the input, else "expected the end of the line".
def Parse.lineEnd(): {Parse} () :=
  if Parse.mark().left == 0 then ()
  else if Parse.literal ['\n'] then ()
  else if Parse.literal ['\r', '\n'] then ()
  else Parse.expected "the end of the line"

-- A line break, a line of nothing but spaces and tabs, and its line break;
-- else "expected a blank line" where it starts.
def Parse.blankLine(): {Parse} () :=
  Parse.labelWhole "a blank line" (() =>
    Parse.newline()
    Parse.spaces()
    Parse.newline())

-- The end of the input, else "expected the end".
def Parse.end(): {Parse} () := if Parse.mark().left == 0 then () else Parse.expected "the end"

-- The value paired with the first word that comes next, as aoc-parse's
-- `{ "L" => …, "R" => … }`; else "expected 'L' or 'R'". Words are tried in
-- order, so put a word before any that start it.
def Parse.pick (choices: List (Text, a)): {Parse} a :=
  match choices.find (choice => Parse.literal choice.fst.toList) with
    | Some (word, value) => value
    | None =>
      Parse.noteWords choices
      Empty.absurd Parse.stop()

-- Notes each word of `pick`'s choices as expected here.
def Parse.noteWords: List (Text, a) → {Parse} ()
  | Nil => ()
  | Cons (word, value) rest =>
    Parse.note (Literal word)
    Parse.noteWords rest

-- Choice and repetition. A failed alternative leaves the input as it was.

-- `Some` of `parser`'s value, or `None` with the input as it was if it
-- fails. Never fails.
def Parse.optional (parser: () → {Parse} a): {Parse} (Option a) := Parse.optionalFrom Parse.mark() parser

-- `optional` once it has marked where it started.
def Parse.optionalFrom (start: Parse.Mark) (parser: () → {Parse} a): {Parse} (Option a) :=
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

-- The value found, else `fallback`'s.
def Parse.valueOr (found: Option a) (fallback: () → {Parse} a): {Parse} a :=
  match found with
    | Some value => value
    | None => fallback()

def Parse.oneOfFrom (first: () → {Parse} a): List (() → {Parse} a) → {Parse} a
  | [] => first()
  | [next, ..rest] => Parse.valueOr (Parse.optional first) (() => Parse.oneOfFrom next rest)

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

-- `parser` while it succeeds, at most `count` more times. `found` is newest first.
def Parse.repeatOptional (count: Nat) (parser: () → {Parse} a) (found: List a): {Parse} (List a) :=
  match count with
    | Zero => found.reverse
    | Succ more =>
      match Parse.optional parser with
        | Some value => Parse.repeatOptional more parser (Cons value found)
        | None => found.reverse

-- `parser` `count` times, failing as it fails, then at most `extra` more
-- times while it succeeds. `found` is newest first.
def Parse.repeatFrom (count: Nat) (extra: Nat) (parser: () → {Parse} a) (found: List a): {Parse} (List a) :=
  match count with
    | Zero => Parse.repeatOptional extra parser found
    | Succ more =>
      let value := parser()
      Parse.repeatFrom more extra parser (Cons value found)

-- `parser`'s values, `atLeast` to `atMost` of them, as Megaparsec's `count'`:
-- the first `atLeast` must match, then it stops at the first failure or at
-- `atMost`. `repeat 3 3 digit` is exactly three digits.
def Parse.repeat (atLeast: Nat) (atMost: Nat) (parser: () → {Parse} a): {Parse} (List a) :=
  Parse.repeatFrom atLeast (atMost - atLeast) parser []

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

-- `parser` on a line after the first of a `section`. If it fails, a blank
-- line before this line is also expected there: the section may have ended.
-- At the end of the input, where there is no line, a blank line is.
def Parse.sectionLine (parser: () → {Parse} a): {Parse} a :=
  let start := Parse.mark()
  handle parser() with
    | return value => value
    | Parse.span passes, k => k (Parse.span passes)
    | Parse.next passes, k => k (Parse.next passes)
    | Parse.literal chars, k => k (Parse.literal chars)
    | Parse.mark u, k => k Parse.mark()
    | Parse.reset at, k => k (Parse.reset at)
    | Parse.note problem, k => k (Parse.note problem)
    | Parse.stop u, k =>
      let here := Parse.mark()
      Parse.note (Expected (if here.left == 0 ∧ here.offset == start.offset then "a blank line" else "a blank line before this line"))
      Empty.absurd Parse.stop()
    | Parse.fatal message, k => Empty.absurd (Parse.fatal message)

-- One `parser` per line, at least one, then a blank line: a section that
-- another follows, as aoc-parse's `section`. For input whose sections hold
-- different things: `section rule`, then `lines update` for the last. If a
-- line after the first fails, a blank line before it is expected too.
def Parse.section (parser: () → {Parse} a): {Parse} (List a) :=
  let first := parser()
  let rest := Parse.many (() =>
    Parse.newline()
    Parse.sectionLine parser)
  Parse.blankLine()
  Cons first rest

-- Rows of cells, one row per line, at least one cell in each. Rows may
-- differ in length.
def Parse.grid (cell: () → {Parse} a): {Parse} (List (List a)) := Parse.lines (() => Parse.many1 cell)

-- One row of `looseGrid`: its cells and its line break, if any. Fails
-- without a problem of its own at the end of the input, where there is no row.
def Parse.looseRow (cell: () → {Parse} a): {Parse} (List a) :=
  if Parse.mark().left == 0 then Empty.absurd Parse.stop()
  else
    let cells := Parse.many cell
    Parse.lineEnd()
    cells

-- Rows of cells, one row per line, as `grid`, but possibly no rows, and a
-- row may have no cells: every line, empty or not, is a row. Never fails
-- at the start of a line; a bad cell is "expected '@' or '.' or the end of
-- the line".
def Parse.looseGrid (cell: () → {Parse} a): {Parse} (List (List a)) := Parse.many (() => Parse.looseRow cell)

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

-- `parser`, but if it fails anywhere, it backs up and fails with "expected
-- `what`" where it started, dropping what it expected inside: for a short
-- token, such as a blank line, that reads best as one thing.
def Parse.labelWhole (what: Text) (parser: () → {Parse} a): {Parse} a :=
  let start := Parse.mark()
  handle parser() with
    | return value => value
    | Parse.span passes, k => k (Parse.span passes)
    | Parse.next passes, k => k (Parse.next passes)
    | Parse.literal chars, k => k (Parse.literal chars)
    | Parse.mark u, k => k Parse.mark()
    | Parse.reset at, k => k (Parse.reset at)
    | Parse.note problem, k => k ()
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

-- What `failure` expected, in words for a runner whose input ends with
-- `endOfInput`: "a line break" and "the end" together are "the end of the
-- line", since either ends it.
def Parse.Failure.expectations (failure: Parse.Failure) (endOfInput: Text): List Text :=
  let endsLine := failure.expected.any (== "a line break") ∧ failure.expected.any (== "the end")
  failure.expected
    |> .filter (what => ¬(endsLine ∧ what == "the end"))
    |> .map (what => if endsLine ∧ what == "a line break" then "the end of the line" else if what == "the end" then endOfInput else what)
    |> .distinctEq

-- What was found `failure.offset` characters into `chars`, for "got 'x'":
-- as many characters as the longest text expected there, up to a line
-- break, as Megaparsec shows; a line break is `lineBreak`, and past the
-- last character is `endOfInput`.
def Parse.Failure.found (failure: Parse.Failure) (chars: List Char) (endOfInput: Text) (lineBreak: Text): Text :=
  let rest := chars.drop failure.offset
  match rest with
    | Nil => endOfInput
    | Cons char after =>
      if char == '\n' ∨ char == '\r' then lineBreak
      else if failure.width > 1 then
        let shown := rest.take failure.width |> .takeWhile (shownChar => shownChar ≠ '\n' ∧ shownChar ≠ '\r') |> Text.fromList
        "'${shown}'"
      else if char == '\t' then "a tab"
      else "'${char}'"

-- `failure` as one message: the parser's own messages, then "expected A or
-- B, got 'x'" with what was found in `chars` instead. `endOfInput` and
-- `lineBreak` name the end of `chars` and a line break in it.
def Parse.Failure.describe (failure: Parse.Failure) (chars: List Char) (endOfInput: Text) (lineBreak: Text): Text :=
  let expectations := failure.expectations endOfInput
  let expectedPart :=
    if expectations == [] then [] else ["expected ${Text.joinWith expectations " or "}, got ${failure.found chars endOfInput lineBreak}"]
  match failure.messages ++ expectedPart with
    | [] => "the parser failed"
    | [only] => only
    | parts => Text.joinWith parts "; "

-- `parser` on all of `input`, else fail with "line 3, column 5: expected
-- ',', got ';'". For input with sections; holds the input as a list of
-- characters, so for large line-per-record input `Parse.eachLine` is faster
-- and smaller. Line breaks at the end of the input are allowed.
def Parse.all (input: Text) (parser: () → {Parse} a): {Fail} a :=
  let chars := input.toList
  let withFinalLineBreaks := () =>
    let value := parser()
    let finalLineBreaks := Parse.span (char => char == '\n' ∨ char == '\r')
    if finalLineBreaks == [] then Parse.note (Expected "a line break") else ()
    value
  match Parse.whole chars withFinalLineBreaks with
    | Ok value => value
    | Err failure =>
      let (line, column) := Parse.lineAndColumn chars failure.offset
      Fail.fail "line ${line}, column ${column}: ${failure.describe chars "the end of the input" "the end of the line"}"

-- `parser` on one line, else fail with "column 5: expected ',', got ';'".
-- One line break at the end is allowed; a failure after a line break gives
-- its line too, as `Parse.all` does.
def Parse.line (line: Text) (parser: () → {Parse} a): {Fail} a :=
  let chars := line.toList
  let withFinalLineBreak := () =>
    let value := parser()
    let finalLineBreak := Parse.optional Parse.newline
    value
  match Parse.whole chars withFinalLineBreak with
    | Ok value => value
    | Err failure =>
      match Parse.lineAndColumn chars failure.offset with
        | (1, column) => Fail.fail "column ${column}: ${failure.describe chars "the end of the line" "a line break"}"
        | (lineNumber, column) =>
          Fail.fail "line ${lineNumber}, column ${column}: ${failure.describe chars "the end of the input" "a line break"}"

-- `parser` on each line of `input`, split as `Text.lines` splits, else fail
-- with "line 3, column 5: expected ',', got ';'" for the first line that
-- fails. Lines are numbered from 1.
def Parse.eachLine (input: Text) (parser: () → {Parse} a): {Fail} (List a) :=
  input.lines.withIndex.map (((index, line)) =>
    let chars := line.toList
    match Parse.whole chars parser with
      | Ok value => value
      | Err failure => Fail.fail "line ${index + 1}, column ${failure.offset + 1}: ${failure.describe chars "the end of the line" "a line break"}")

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
    Parse.runFrom state (() => k (Parse.fatal message)) = Err ({ offset = state.at.offset, messages = [message], expected = [], width = 0 }) := rfl

theorem Parse.runFromSpan (state: Parse.State) (passes: Char → Bool) (k: List Char → {Parse} a):
    Parse.runFrom state (() => k (Parse.span passes)) =
      Parse.runFrom (state.advance (state.at.rest.span passes).snd (state.at.rest.span passes).fst.length) (() => k (state.at.rest.span passes).fst) :=
  rfl

-- `literal` where the input starts with the characters: it reads them.
theorem Parse.runFromLiteralThere (state: Parse.State) (chars: List Char) (rest: List Char) (k: Bool → {Parse} a)
    (starts: state.at.rest = List.append chars rest):
    Parse.runFrom state (() => k (Parse.literal chars)) = Parse.runFrom (state.advance rest chars.length) (() => k True) :=
  rewrite starts, Text.stripPrefixCharsAppend rest chars

-- `span` where the input starts with `taken`, all passing, and the character
-- after them (if any) doesn't: it reads `taken`.
theorem Parse.runFromSpanThere (state: Parse.State) (passes: Char → Bool) (taken: List Char) (rest: List Char) (k: List Char → {Parse} a)
    (starts: state.at.rest = List.append taken rest) (all: List.all taken passes = True) (stops: List.takeWhile rest passes = Nil):
    Parse.runFrom state (() => k (Parse.span passes)) = Parse.runFrom (state.advance rest taken.length) (() => k taken) :=
  rewrite Parse.runFromSpan state passes k, starts, List.spanAppend passes taken rest all stops in rfl

-- `next` where the next character passes: it reads it.
theorem Parse.runFromNextThere (state: Parse.State) (passes: Char → Bool) (char: Char) (rest: List Char) (k: Option Char → {Parse} a)
    (starts: state.at.rest = Cons char rest) (holds: passes char = True):
    Parse.runFrom state (() => k (Parse.next passes)) = Parse.runFrom (state.advance rest 1) (() => k (Some char)) :=
  rewrite starts, holds in rfl

-- What each piece does where the input has what it reads. Each holds by
-- `rewrite` and `rfl`.

theorem Parse.runFromTextThere (state: Parse.State) (expected: Text) (rest: List Char) (k: () → {Parse} a)
    (starts: state.at.rest = List.append expected.toList rest):
    Parse.runFrom state (() => k (Parse.text expected)) = Parse.runFrom (state.advance rest expected.toList.length) (() => k ()) :=
  rewrite starts, Text.stripPrefixCharsAppend rest expected.toList in rfl

theorem Parse.sameChar (char: Char): (char == char) = True :=
  match Char.decEq char char with
    | Yes same => rfl
    | No different => Void.exfalso (different rfl)

theorem Parse.runFromCharThere (state: Parse.State) (expected: Char) (rest: List Char) (k: () → {Parse} a)
    (starts: state.at.rest = Cons expected rest):
    Parse.runFrom state (() => k (Parse.char expected)) = Parse.runFrom (state.advance rest 1) (() => k ()) :=
  rewrite starts, Parse.sameChar expected in rfl

-- `nat` on a run of digits, followed by something else or nothing.
theorem Parse.runFromNatThere (state: Parse.State) (digits: List Char) (rest: List Char) (k: Nat → {Parse} a)
    (starts: state.at.rest = List.append digits rest) (some: digits ≠ Nil) (all: List.all digits Parse.isDigit = True)
    (stops: List.takeWhile rest Parse.isDigit = Nil):
    Parse.runFrom state (() => k (Parse.nat())) =
      Parse.runFrom (state.advance rest digits.length) (() => k (digits.map (digit => digit.digitValue.getOrElse 0) |> Nat.fromDigits)) :=
  match digits with
    | Nil => Void.exfalso (some rfl)
    | Cons first others => rewrite starts, List.spanAppend Parse.isDigit (Cons first others) rest all stops in rfl

theorem Parse.runFromEndThere (state: Parse.State) (k: () → {Parse} a) (atEnd: state.at.left = 0):
    Parse.runFrom state (() => k (Parse.end())) = Parse.runFrom state (() => k ()) :=
  rewrite atEnd in rfl

-- `optional` marks where it starts, then runs the parser under
-- `optionalFrom`, which passes each reading operation on, gives `Some` of a
-- value, and backs up to the mark on a failure. So a run of `optional
-- parser` follows the parser's own operations.

theorem Parse.runFromOptional (state: Parse.State) (parser: () → {Parse} a) (k: Option a → {Parse} b):
    Parse.runFrom state (() => k (Parse.optional parser)) = Parse.runFrom state (() => k (Parse.optionalFrom state.at parser)) := rfl

theorem Parse.runFromOptionalFromSpan (state: Parse.State) (start: Parse.Mark) (passes: Char → Bool) (rest: List Char → {Parse} a)
    (k: Option a → {Parse} b):
    Parse.runFrom state (() => k (Parse.optionalFrom start (() => rest (Parse.span passes)))) =
      Parse.runFrom state (() =>
        let taken := Parse.span passes
        k (Parse.optionalFrom start (() => rest taken))) :=
  rfl

theorem Parse.runFromOptionalFromNext (state: Parse.State) (start: Parse.Mark) (passes: Char → Bool) (rest: Option Char → {Parse} a)
    (k: Option a → {Parse} b):
    Parse.runFrom state (() => k (Parse.optionalFrom start (() => rest (Parse.next passes)))) =
      Parse.runFrom state (() =>
        let found := Parse.next passes
        k (Parse.optionalFrom start (() => rest found))) :=
  rfl

theorem Parse.runFromOptionalFromLiteral (state: Parse.State) (start: Parse.Mark) (chars: List Char) (rest: Bool → {Parse} a)
    (k: Option a → {Parse} b):
    Parse.runFrom state (() => k (Parse.optionalFrom start (() => rest (Parse.literal chars)))) =
      Parse.runFrom state (() =>
        let found := Parse.literal chars
        k (Parse.optionalFrom start (() => rest found))) :=
  rfl

-- Success: the parser has given a value.
theorem Parse.runFromOptionalFromPure (state: Parse.State) (start: Parse.Mark) (value: a) (k: Option a → {Parse} b):
    Parse.runFrom state (() => k (Parse.optionalFrom start (() => value))) = Parse.runFrom state (() => k (Some value)) := rfl

-- Backtracking: the parser has failed, so the input is as it was at the mark.
theorem Parse.runFromOptionalFromStop (state: Parse.State) (start: Parse.Mark) (rest: Empty → {Parse} a) (k: Option a → {Parse} b):
    Parse.runFrom state (() => k (Parse.optionalFrom start (() => rest Parse.stop()))) = Parse.runFrom { state | at = start } (() => k None) :=
  rfl

-- Both cases for a piece, `text`.
theorem Parse.runFromOptionalTextThere (state: Parse.State) (expected: Text) (rest: List Char) (k: Option () → {Parse} a)
    (starts: state.at.rest = List.append expected.toList rest):
    Parse.runFrom state (() => k (Parse.optional (() => Parse.text expected))) =
      Parse.runFrom (state.advance rest expected.toList.length) (() => k (Some ())) :=
  rewrite starts, Text.stripPrefixCharsAppend rest expected.toList in rfl

theorem Parse.runFromOptionalTextNotThere (state: Parse.State) (expected: Text) (k: Option () → {Parse} a)
    (absent: Text.stripPrefixChars expected.toList state.at.rest = None):
    Parse.runFrom state (() => k (Parse.optional (() => Parse.text expected))) =
      Parse.runFrom { state.note (Literal expected) | at = state.at } (() => k None) :=
  rewrite absent in rfl

-- `oneOf` with an alternative after `first`: if `optional first` succeeds,
-- whatever follows it, `first`'s value; if it backs up, the rest.
theorem Parse.runFromOneOfFromSome (state: Parse.State) (after: Parse.State) (first: () → {Parse} a) (next: () → {Parse} a)
    (rest: List (() → {Parse} a)) (value: a) (k: a → {Parse} b)
    (succeeds: (choose: Option a → {Parse} a) → (finish: a → {Parse} b) →
      Parse.runFrom state (() => finish (choose (Parse.optional first))) = Parse.runFrom after (() => finish (choose (Some value)))):
    Parse.runFrom state (() => k (Parse.oneOfFrom first (Cons next rest))) = Parse.runFrom after (() => k value) :=
  succeeds (found => Parse.valueOr found (() => Parse.oneOfFrom next rest)) k

theorem Parse.runFromOneOfFromNone (state: Parse.State) (after: Parse.State) (first: () → {Parse} a) (next: () → {Parse} a)
    (rest: List (() → {Parse} a)) (k: a → {Parse} b)
    (fails: (choose: Option a → {Parse} a) → (finish: a → {Parse} b) →
      Parse.runFrom state (() => finish (choose (Parse.optional first))) = Parse.runFrom after (() => finish (choose None))):
    Parse.runFrom state (() => k (Parse.oneOfFrom first (Cons next rest))) = Parse.runFrom after (() => k (Parse.oneOfFrom next rest)) :=
  fails (found => Parse.valueOr found (() => Parse.oneOfFrom next rest)) k

-- The last alternative is run as it is.
theorem Parse.runFromOneOfFromLast (state: Parse.State) (only: () → {Parse} a) (k: a → {Parse} b):
    Parse.runFrom state (() => k (Parse.oneOfFrom only [])) = Parse.runFrom state (() => k (only())) := rfl

-- With concrete alternatives the run computes: the first of two words.
theorem Parse.runFromOneOfExample (state: Parse.State) (rest: List Char) (k: Nat → {Parse} b)
    (starts: state.at.rest = List.append "ab".toList rest):
    Parse.runFrom state (() =>
      k (Parse.oneOf [
        () =>
          Parse.text "ab"
          1,
        () =>
          Parse.text "cd"
          2
      ])) = Parse.runFrom (state.advance rest 2) (() => k 1) :=
  rewrite starts in rfl

theorem Parse.runPure (input: List Char) (value: a): Parse.run input (() => value) = Ok value := rfl

theorem Parse.runFail (message: Text): Parse.run [] (() => (Parse.fail message: Nat)) = Err ({ offset = 0, messages = [message], expected = [], width = 0 }) := rfl

-- Tests. Each runs a parser with `Parse.line` (errors give the column) or
-- `Parse.all` (the line and column).

def Parse.Tests.lineResult (line: Text) (parser: () → {Parse} a): Result a Text := Fail.toResult (() => Parse.line line parser)

def Parse.Tests.allResult (input: Text) (parser: () → {Parse} a): Result a Text := Fail.toResult (() => Parse.all input parser)

-- The error if `parser` fails on `line`, else "": for parsers whose value is `()`.
def Parse.Tests.lineError (line: Text) (parser: () → {Parse} a): Text := Parse.Tests.lineResult line parser |> .errorOrElse ""

test "Parse: char" := Parse.Tests.lineError "a" (() => Parse.char 'a') == ""
test "Parse: char, error" := Parse.Tests.lineError "b" (() => Parse.char 'a') == "column 1: expected 'a', got 'b'"
test "Parse: text" := Parse.Tests.lineResult "p=4" (() =>
  Parse.text "p="
  Parse.nat()) == Ok 4
test "Parse: text, error" := Parse.Tests.lineError "p-4" (() => Parse.text "p=") == "column 1: expected 'p=', got 'p-'"
test "Parse: satisfy" := Parse.Tests.lineResult "e" (() => Parse.satisfy "a vowel" (char => "aeiou".toList.any (== char))) == Ok 'e'
test "Parse: satisfy, error" :=
  Parse.Tests.lineResult "x" (() => Parse.satisfy "a vowel" (char => "aeiou".toList.any (== char))) == Err "column 1: expected a vowel, got 'x'"
test "Parse: takeWhile" := Parse.Tests.lineResult "aab" (() =>
  let run := Parse.takeWhile (== 'a')
  Parse.char 'b'
  run) == Ok "aa"
test "Parse: takeWhile, none" := Parse.Tests.lineResult "" (() => Parse.takeWhile (== 'a')) == Ok ""
test "Parse: takeWhile1" := Parse.Tests.lineResult "aa" (() => Parse.takeWhile1 "an a" (== 'a')) == Ok "aa"
test "Parse: takeWhile1, error" := Parse.Tests.lineResult "b" (() => Parse.takeWhile1 "an a" (== 'a')) == Err "column 1: expected an a, got 'b'"
test "Parse: nat" := Parse.Tests.lineResult "1203" Parse.nat == Ok 1203
test "Parse: nat, error" := Parse.Tests.lineResult "x" Parse.nat == Err "column 1: expected a number, got 'x'"
test "Parse: nat, then the end" := Parse.Tests.lineResult "12x" Parse.nat == Err "column 3: expected the end of the line, got 'x'"
test "Parse: int" := Parse.Tests.lineResult "-12" Parse.int == Ok (-12)
test "Parse: int, positive" := Parse.Tests.lineResult "12" Parse.int == Ok 12
test "Parse: int, error" := Parse.Tests.lineResult "-" Parse.int == Err "column 2: expected a number, got the end of the line"
test "Parse: digit" := Parse.Tests.lineResult "7" (() => Parse.digit().toNat) == Ok 7
test "Parse: digit, error" := Parse.Tests.lineResult "x" (() => Parse.digit().toNat) == Err "column 1: expected a digit, got 'x'"
test "Parse: spaces" := Parse.Tests.lineResult " \t 5" (() =>
  Parse.spaces()
  Parse.nat()) == Ok 5
test "Parse: spaces1" := Parse.Tests.lineResult " 5" (() =>
  Parse.spaces1()
  Parse.nat()) == Ok 5
test "Parse: spaces1, error" := Parse.Tests.lineError "5" Parse.spaces1 == "column 1: expected a space, got '5'"
test "Parse: token" := Parse.Tests.lineResult " 1 \t2 " (() => Parse.many1 (() => Parse.token Parse.nat)) == Ok [1, 2]
test "Parse: token, error" := Parse.Tests.lineResult " 1 x" (() => Parse.many1 (() => Parse.token Parse.nat)) == Err "column 4: expected a number or the end of the line, got 'x'"
test "Parse: newline" := Parse.Tests.lineResult "1\n2" (() => Parse.sepBy1 Parse.nat Parse.newline) == Ok [1, 2]
test "Parse: newline, CRLF" := Parse.Tests.lineResult "1\r\n2" (() => Parse.sepBy1 Parse.nat Parse.newline) == Ok [1, 2]
test "Parse: newline, error" := Parse.Tests.lineError "x" Parse.newline == "column 1: expected a line break, got 'x'"
test "Parse: blankLine" := Parse.Tests.lineError "\n\n" Parse.blankLine == ""
test "Parse: blankLine, error" := Parse.Tests.lineError "x" Parse.blankLine == "column 1: expected a blank line, got 'x'"
test "Parse: blankLine, spaces" := Parse.Tests.lineError "\n \t\n" Parse.blankLine == ""
-- A blank line that fails part way is reported where it starts.
test "Parse: blankLine, a line that is not blank" := Parse.Tests.lineError "\n x\n" Parse.blankLine == "column 1: expected a blank line, got a line break"
test "Parse: lineEnd" := Parse.Tests.lineResult "1\n2" (() => Parse.sepBy1 (() => Parse.nat()) Parse.lineEnd) == Ok [1, 2]
test "Parse: lineEnd, error" := Parse.Tests.lineError "x" Parse.lineEnd == "column 1: expected the end of the line, got 'x'"
test "Parse: end" := Parse.Tests.lineError "" Parse.end == ""
test "Parse: pick" := Parse.Tests.lineResult "R" (() => Parse.pick [("L", 1), ("R", 2)]) == Ok 2
test "Parse: pick, error" := Parse.Tests.lineResult "X" (() => Parse.pick [("L", 1), ("R", 2)]) == Err "column 1: expected 'L' or 'R', got 'X'"
-- What was found is shown as long as the longest word expected.
test "Parse: pick, error, longer words" :=
  Parse.Tests.lineResult "mul ( 1,2)" (() => Parse.pick [("mul(", 1), ("do()", 2), ("don't()", 3)]) ==
    Err "column 1: expected 'mul(' or 'do()' or 'don't()', got 'mul ( 1'"
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
  ]) == "column 2: expected 'b' or 'c', got 'd'"
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
test "Parse: many1, error" := Parse.Tests.lineResult "" (() => Parse.many1 (() => Parse.satisfy "an a" (== 'a'))) == Err "column 1: expected an a, got the end of the line"
test "Parse: sepBy" := Parse.Tests.lineResult "1,2,3" (() => Parse.sepBy Parse.nat (() => Parse.char ',')) == Ok [1, 2, 3]
test "Parse: sepBy, none" := Parse.Tests.lineResult "" (() => Parse.sepBy Parse.nat (() => Parse.char ',')) == Ok []
test "Parse: sepBy1, error" := Parse.Tests.lineResult "1,2," (() => Parse.sepBy1 Parse.nat (() => Parse.char ',')) == Err "column 5: expected a number, got the end of the line"
test "Parse: lines" := Parse.Tests.allResult "1\n2\n" (() => Parse.lines Parse.nat) == Ok [1, 2]
test "Parse: lines, error" := Parse.Tests.allResult "1\n2\nx\n" (() => Parse.lines Parse.nat) == Err "line 3, column 1: expected a number or the end of the input, got 'x'"
test "Parse: sections" := Parse.Tests.allResult "1\n2\n\n3\n" (() => Parse.sections (() => Parse.lines Parse.nat)) == Ok [[1, 2], [3]]
test "Parse: grid" :=
  Parse.Tests.allResult "@.\n.@\n" (() => Parse.grid (() => Parse.pick [("@", True), (".", False)])) == Ok [[True, False], [False, True]]
test "Parse: grid, error" :=
  Parse.Tests.allResult "@.\n.x\n" (() => Parse.grid (() => Parse.pick [("@", True), (".", False)])) ==
    Err "line 2, column 2: expected '@' or '.' or the end of the line, got 'x'"
test "Parse: looseGrid" :=
  Parse.Tests.allResult "@.\n\n.\n" (() => Parse.looseGrid (() => Parse.pick [("@", True), (".", False)])) == Ok [[True, False], [], [False]]
test "Parse: looseGrid, no rows" := Parse.Tests.allResult "" (() => Parse.looseGrid (() => Parse.pick [("@", True), (".", False)])) == Ok []
test "Parse: looseGrid, error" :=
  Parse.Tests.allResult "@.\n.x\n" (() => Parse.looseGrid (() => Parse.pick [("@", True), (".", False)])) ==
    Err "line 2, column 2: expected '@' or '.' or the end of the line, got 'x'"
test "Parse: label" :=
  Parse.Tests.lineResult "X5" (() => Parse.label "a turn like L68" (() => Parse.pick [("L", 1), ("R", 2)])) ==
    Err "column 1: expected a turn like L68, got 'X'"
-- A labelled parser that got further reports what it expected there.
test "Parse: label, further in" := Parse.Tests.lineResult "1,x" (() =>
  Parse.label "a pair like 1,2" (() =>
    let left := Parse.nat()
    Parse.char ','
    (left, Parse.nat()))) == Err "column 3: expected a number, got 'x'"

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
  Parse.Tests.lineResult "[1,[2,x]]" Parse.Tests.nestedSum == Err "column 7: expected a number or '[', got 'x'"
test "Parse: recursive, left recursion" := Parse.Tests.lineResult "1+2" (() =>
  Parse.recursive (self =>
    let left := self()
    Parse.char '+'
    left + Parse.nat())) ==
  Err "column 1: `recursive`: the parser called itself without reading anything"

test "Parse: fail" := Parse.Tests.lineResult "a" (() => (Parse.fail "no": Nat)) == Err "column 1: no"
test "Parse: expected" := Parse.Tests.lineResult "a" (() => (Parse.expected "a b": Nat)) == Err "column 1: expected a b, got 'a'"
-- A message and an expectation at the same point are both reported.
test "Parse: fail beside expected" := Parse.Tests.lineError "y" (() =>
  Parse.oneOf [
    () => Parse.fail "not this",
    () => Parse.char 'x'
  ]) == "column 1: not this; expected 'x', got 'y'"
test "Parse: ensure" := Parse.Tests.lineResult "5" (() =>
  let number := Parse.nat()
  Parse.ensure (number > 9) "too small"
  number) == Err "column 2: too small"
-- What `many1` tried after the last digit is dropped for the message.
test "Parse: ensure after a repetition" := Parse.Tests.lineResult "12" (() =>
  let digits := Parse.many1 Parse.digit
  Parse.ensure (digits.length > 2) "too few digits"
  digits.length) == Err "column 3: too few digits"
-- A tab and the end of the input are named, not shown.
test "Parse: got a tab" := Parse.Tests.lineError "\t" (() => Parse.char 'a') == "column 1: expected 'a', got a tab"
test "Parse: got the end of the input" := Parse.Tests.allResult "1," (() => Parse.sepBy1 Parse.nat (() => Parse.char ',')) == Err "line 1, column 3: expected a number, got the end of the input"
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
    Err "line 2, column 2: expected ',' or the end of the line, got ';'"
test "Parse: all, one line" :=
  Parse.Tests.allResult "1,2x" (() => Parse.sepBy1 Parse.nat (() => Parse.char ',')) == Err "line 1, column 4: expected ',' or the end of the line, got 'x'"
test "Parse: eachLine" :=
  Fail.toResult (() => Parse.eachLine "1,2\n3,4\n" (() => Parse.sepBy1 Parse.nat (() => Parse.char ','))) == Ok [[1, 2], [3, 4]]
test "Parse: eachLine, error" :=
  Fail.toResult (() => Parse.eachLine "1,2\n3x4" (() => Parse.sepBy1 Parse.nat (() => Parse.char ','))) ==
    Err "line 2, column 2: expected ',' or the end of the line, got 'x'"
test "Parse: eachLine, empty" := Fail.toResult (() => Parse.eachLine "" Parse.nat) == Ok []
-- A failure keeps its line under `Fail.context`.
test "Parse: eachLine, in context" :=
  Fail.toResult (() => Fail.context "input" (() => Parse.eachLine "x" Parse.nat)) == Err "input: line 1, column 1: expected a number, got 'x'"
test "Parse: all, trailing blank lines" := Parse.Tests.allResult "1\n2\n\n\n" (() => Parse.lines Parse.nat) == Ok [1, 2]
test "Parse: line, a final line break" := Parse.Tests.lineResult "12\n" Parse.nat == Ok 12
test "Parse: line, two final line breaks" :=
  Parse.Tests.lineResult "12\n\n" Parse.nat == Err "line 2, column 1: expected the end of the input, got a line break"
test "Parse: line, a second line" := Parse.Tests.lineResult "12\n34\n" Parse.nat == Err "line 2, column 1: expected the end of the input, got '3'"
test "Parse: line, an error on a second line" :=
  Parse.Tests.lineResult "1\n2x" (() => Parse.sepBy1 Parse.nat Parse.newline) == Err "line 2, column 2: expected the end of the line, got 'x'"

test "Parse: ensureAt" := Parse.Tests.lineResult "x=12345" (() =>
  Parse.text "x="
  let start := Parse.mark()
  let number := Parse.nat()
  let finish := Parse.mark()
  Parse.ensureAt start (finish.offset - start.offset ≤ 3) "too long"
  number) == Err "column 3: too long"
test "Parse: natDigits" := Parse.Tests.lineResult "123" (() => Parse.natDigits 1 3) == Ok 123
test "Parse: natDigits, too long" := Parse.Tests.lineResult "x1234" (() =>
  Parse.char 'x'
  Parse.natDigits 1 3) == Err "column 2: expected a number of 1 to 3 digits, got '1'"
test "Parse: natDigits, too short" := Parse.Tests.lineResult "12" (() => Parse.natDigits 3 3) == Err "column 1: expected a number of 3 digits, got '1'"
test "Parse: natDigits, none" := Parse.Tests.lineResult "x" (() => Parse.natDigits 0 3) == Err "column 1: expected a number of 0 to 3 digits, got 'x'"
test "Parse: repeat" := Parse.Tests.lineResult "aab" (() =>
  let found := Parse.repeat 1 3 (() => Parse.satisfy "an a" (== 'a'))
  Parse.char 'b'
  found) == Ok ['a', 'a']
test "Parse: repeat, at most" := Parse.Tests.lineResult "aaaa" (() =>
  let found := Parse.repeat 1 3 (() => Parse.satisfy "an a" (== 'a'))
  Parse.char 'a'
  found) == Ok ['a', 'a', 'a']
test "Parse: repeat, too few" := Parse.Tests.lineResult "ab" (() => Parse.repeat 2 3 (() => Parse.satisfy "an a" (== 'a'))) == Err "column 2: expected an a, got 'b'"
test "Parse: repeat, exactly" := Parse.Tests.lineResult "123" (() => Parse.repeat 3 3 Parse.digit |> .map (digit => digit.toNat)) == Ok [1, 2, 3]

-- The values of `nat` among other characters.
def Parse.Tests.numbers (line: Text): Result (List Nat) Text := Parse.Tests.lineResult line (() => Parse.findAll Parse.nat)

test "Parse: findAll" := Parse.Tests.numbers "a1b22c333" == Ok [1, 22, 333]
test "Parse: findAll, none" := Parse.Tests.numbers "abc" == Ok []
test "Parse: findAll, empty input" := Parse.Tests.numbers "" == Ok []
-- A failed try reads nothing, so a match can start inside it.
test "Parse: findAll, inside a failed try" := Parse.Tests.lineResult "aab" (() => Parse.findAll (() => Parse.text "ab")) == Ok [()]
test "Parse: findAll, a match that reads nothing" := Parse.Tests.lineResult "ab" (() => Parse.findAll (() => Parse.mark().offset)) == Ok [0, 1, 2]
test "Parse: findAllStarting" := Parse.Tests.lineResult "a1b22c333" (() => Parse.findAllStarting Parse.isDigit Parse.nat) == Ok [1, 22, 333]

-- Two sections of different things: rules like "1|2", a blank line, then
-- lists like "1,2".
def Parse.Tests.twoSections (input: Text): Result (List (Nat, Nat), List (List Nat)) Text :=
  Parse.Tests.allResult input (() =>
    let rules := Parse.section (() =>
      let before := Parse.nat()
      Parse.char '|'
      (before, Parse.nat()))
    let lists := Parse.lines (() => Parse.sepBy1 Parse.nat (() => Parse.char ','))
    (rules, lists))

test "Parse: section" := Parse.Tests.twoSections "1|2\n3|4\n\n1,2\n3\n" == Ok ([(1, 2), (3, 4)], [[1, 2], [3]])
test "Parse: section, trailing blank lines" := Parse.Tests.twoSections "1|2\n\n1,2\n\n\n" == Ok ([(1, 2)], [[1, 2]])
test "Parse: section, no blank line" :=
  Parse.Tests.twoSections "1|2\n1,2\n" == Err "line 2, column 2: expected '|' or a blank line before this line, got ','"
test "Parse: section, a bad line" := Parse.Tests.twoSections "1|2\n3x4\n\n1,2\n" == Err "line 2, column 2: expected '|' or a blank line before this line, got 'x'"
test "Parse: section, a bad first line" := Parse.Tests.twoSections "1x2\n\n1,2\n" == Err "line 1, column 2: expected '|', got 'x'"
test "Parse: section, blank line of spaces" := Parse.Tests.twoSections "1|2\n  \n1,2\n" == Ok ([(1, 2)], [[1, 2]])
test "Parse: section, nothing after" := Parse.Tests.twoSections "1|2\n3|4\n" == Err "line 3, column 1: expected a number or a blank line, got the end of the input"
