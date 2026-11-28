import Parse.Associativity (LeftAssociative, RightAssociative)
import Parse.Problem (Expected, Literal, Literals, Message)

--| `Parse`: read text into the program's own types. A parser is ordinary
--| direct-style code that uses the `Parse` ability, `() → {Parse Char} a`
--| for a parser of text, as in Unison's parser libraries; a runner
--| (`Parse.all`, `Parse.eachLine`, `Parse.line`) gives it the input.
--| `Parse t` reads a list of `t`: the operations, combinators and their
--| lemmas here work for any `t`, and the character pieces (`char`, `nat`,
--| `word`, Parse/Chars.sw) for `Char`.
--|
--|   import Std.Parse (char, nat)
--|
--|   type Point = { x: Nat, y: Nat }
--|
--|   def point(): {Parse Char} Point :=
--|     let x := nat()
--|     char ','
--|     let y := nat()
--|     { x, y }
--|
--|   def parsePoints (input: Text): {Fail} (List Point) := Parse.eachLine input point
--|
--| A bad line fails with "line 3, column 4: expected ',', got ';'".
--|
--| Choice always backs up: when an alternative of `oneOf`, `optional` or
--| `many` fails, the input is as it was before it. Errors name the furthest
--| point any alternative reached, everything expected there, and what was
--| found there instead. A loop or a recursive grammar that would run
--| forever without reading stops the whole parse with a message naming the
--| combinator.

--| Where a parse is: the items left, how many were read before them,
--| and how many there are.
type Parse.Mark (t: Type) = { rest: List t, offset: Nat, left: Nat }

--| What `Parse.literal` looks for: `items` in a row, each compared with
--| what comes next by `same`. Characters compare with `Text.sameChar`; a
--| token that records where it was read compares by everything but that.
type Parse.Literal (t: Type) = { items: List t, same: t → t → Bool }

--| Why a parse failed at some point: something that was expected there, a
--| text that was expected there, several texts that were (`Literals ws` is
--| noted and shown exactly as `Literal w` for each `w` of `ws`, in order, but
--| costs one operation), or a message of the parser's own.
type Parse.Problem =
  | Expected (what: Text)
  | Literal (text: Text)
  | Literals (texts: List Text)
  | Message (text: Text)

--| A failed parse, `offset` items in: the parser's own messages and
--| what was expected there. A runner makes one message of it with
--| `Parse.Failure.describe`.
type Parse.Failure = {
  offset: Nat,
  messages: List Text,
  expected: List Text,
  width: Nat
}

--| Parsing a list of `t`, text when `t` is `Char`: the operations a parser
--| performs on its input, run by a handler such as `Parse.run`. Each is a
--| token's worth of work in the handler, so a parser makes a handful of them
--| per line, not one per item.
ability Parse (t: Type) where
  --| The longest prefix whose items all pass the test, read.
  span: (t → Bool) → {Parse t} List t
  --| The next item, read if it passes the test.
  next: (t → Bool) → {Parse t} Option t
  --| Reads the literal's items if they come next; whether they did.
  literal: Parse.Literal t → {Parse t} Bool
  --| Where the parse is.
  mark: () → {Parse t} Parse.Mark t
  --| Goes back to a mark.
  reset: Parse.Mark t → {Parse t} ()
  --| Notes a problem at the current point, for the error message.
  note: Parse.Problem → {Parse t} ()
  --| Fails here; the nearest choice backs up.
  stop: () → {Parse t} Empty
  --| Fails the whole parse with this message: no choice backs up. For bugs
  --| in a parser, such as a loop that would never end.
  fatal: Text → {Parse t} Empty

--| What the handler keeps: where the parse is, and the furthest problem noted.
--| That is the furthest point a problem was noted at, with the problems noted
--| there. `expected` holds the `Expected` and `Literal` problems, newest
--| first and unformatted, so noting one is a cons; `Parse.State.failure`
--| makes the texts, without repeats, only when the parse fails.
type Parse.State (t: Type) = {
  at: Parse.Mark t,
  furthest: Nat,
  expected: List Parse.Problem,
  messages: List Text
}

--| The state with a problem noted at the current point.
def Parse.State.add (state: Parse.State t): (problem: Parse.Problem) → Parse.State t
  | Message text => if state.messages.any (== text) then state else { state | messages = state.messages ++ [text] }
  | problem => { state | expected = [problem, ..state.expected] }

--| A problem at the current point replaces those noted nearer the start,
--| joins those noted here, and is dropped if the parse got further before.
--| What was expected here before a message is from attempts that didn't
--| fail the parse, such as the digit `many digit` tried after the last one,
--| so a message replaces it, as Megaparsec's `fail` drops its hints.
def Parse.State.note (state: Parse.State t) (problem: Parse.Problem): Parse.State t :=
  if state.at.offset > state.furthest then
    Parse.State.add { state | furthest = state.at.offset, expected = [], messages = [] } problem
  else if state.at.offset == state.furthest then
    match problem with
      | Message text => Parse.State.add { state | expected = [] } problem
      | _ => state.add problem
  else state

--| The state moved on past `count` items, with `rest` left to read.
def Parse.State.advance (state: Parse.State t) (rest: List t) (count: Nat): Parse.State t :=
  { state | at = { rest, offset = state.at.offset + count, left = state.at.left - count } }

--| The last item read between two marks, `start` and the later `finish` (of
--| the same parse), or `None` if nothing was. For what must be known about
--| the item an element of the grammar ended on, such as a comment that
--| follows a token: `let start := Parse.mark()`, read the element, then
--| `Parse.lastRead start Parse.mark()`. It walks `start`'s items up to that
--| one, so it costs what reading them did; a mark that carried the last item
--| would make it free, but each read would then have to keep it.
def Parse.lastRead (start finish: Parse.Mark t): Option t :=
  if finish.offset > start.offset then start.rest.drop (finish.offset - start.offset - 1) |> .head else None

--| What each reading operation gives, and the state after it, as one pair.
-- `runFrom` doesn't call these: it resumes in each arm of its own `match`,
-- which keeps the handler a loop. They state what it does, for the lemmas:
-- `Parse.runFromNext` and `Parse.runFromLiteral` are stated with them, and the
-- tree lemmas of Parse/Reads.sw use `s.span` (definitionally equal to the
-- handler's step).
def Parse.State.span (state: Parse.State t) (passes: t → Bool): (List t, Parse.State t) :=
  let split := state.at.rest.span passes
  (split.fst, state.advance split.snd split.fst.length)

--| The next item, if it passes the test, and the state after reading it.
def Parse.State.next (state: Parse.State t) (passes: t → Bool): (Option t, Parse.State t) := match state.at.rest with
  | [char, ..after] => if passes char then (Some char, state.advance after 1) else (None, state)
  | [] => (None, state)

--| Whether the literal's items come next, and the state after reading them if they do.
def Parse.State.literal (state: Parse.State t) (literal: Parse.Literal t): (Bool, Parse.State t) :=
  match List.stripPrefixBy state.at.rest literal.items literal.same with
    | Some after => (True, state.advance after literal.items.length)
    | None => (False, state)

--| How a problem reads in a failure's `expected`.
def Parse.Problem.shown: (problem: Parse.Problem) → List Text
  | Expected what => [what]
  | Literal text => ["'${text}'"]
  | Literals texts => texts.map (text => "'${text}'")
  | Message text => [text]

--| `texts` oldest first, without repeats (the first of each kept).
-- `kept` is what has been kept so far, newest first.
@[tailrec]
def Parse.uniqueTexts (kept: List Text): (texts: List Text) → List Text
  | [] => kept.reverse
  | [text, ..rest] => if kept.any (== text) then Parse.uniqueTexts kept rest else Parse.uniqueTexts [text, ..kept] rest

--| The length of the longest `Literal` text among the problems.
def Parse.Problem.widest (problems: List Parse.Problem): Nat := problems.foldLeft 0 (width problem =>
  match problem with
    | Literal text => Nat.max width text.length
    | Literals texts => texts.foldLeft width (width text => Nat.max width text.length)
    | _ => width)

--| The furthest point and its problems.
def Parse.State.failure (state: Parse.State t): Parse.Failure := {
  offset = state.furthest,
  messages = state.messages,
  expected = Parse.uniqueTexts [] (state.expected.reverse.concatMap Parse.Problem.shown),
  width = Parse.Problem.widest state.expected
}

--| Runs `parser` from `state`: its value, or where and why it failed.
def Parse.runFrom (initial: Parse.State t) (parser: () → {Parse t} a): Result a Parse.Failure :=
  let go: Parse.State t → Result a Parse.Failure :=
    handle parser() with
      | return value => state => Ok value
      | Parse.span passes, k => state =>
        let (taken, after) := state.at.rest.span passes
        k taken (state.advance after taken.length)
      | Parse.next passes, k => state =>
        match state.at.rest with
          | [char, ..after] => if passes char then k (Some char) (state.advance after 1) else k None state
          | [] => k None state
      | Parse.literal literal, k => state =>
        match List.stripPrefixBy state.at.rest literal.items literal.same with
          | Some after => k True (state.advance after literal.items.length)
          | None => k False state
      | Parse.mark u, k => state => k state.at state
      | Parse.reset at, k => state => k () { state | at }
      | Parse.note problem, k => state => k () (state.note problem)
      | Parse.stop u, k => state => Err state.failure
      | Parse.fatal message, k => state =>
        Err { offset = state.at.offset, messages = [message], expected = [], width = 0 }
  go initial

--| The state at the start of `input`.
def Parse.State.start (input: List t): Parse.State t :=
  { at = { rest = input, offset = 0, left = input.length }, furthest = 0, expected = [], messages = [] }

--| Runs `parser` from the start of `input`: its value, or where and why it
--| failed. It needn't read all of the input.
def Parse.run (input: List t) (parser: () → {Parse t} a): Result a Parse.Failure :=
  Parse.runFrom (Parse.State.start input) parser

-- Failing. Each fails at the current point: the nearest choice backs up,
-- and if nothing gets further the message is reported here.

--| Fails with `message`, whatever result was expected. It replaces what
--| attempts that didn't fail the parse expected here: `ensure` after `many1
--| digit` gives its own message, without "or a digit".
def Parse.fail (message: Text): {Parse t} a :=
  Parse.note (Message message)
  Empty.absurd Parse.stop()

--| Fails with "expected `what`"; other expectations at the same point are
--| joined to it with "or".
def Parse.expected (what: Text): {Parse t} a :=
  Parse.note (Expected what)
  Empty.absurd Parse.stop()

--| Fails with `message` unless `ok`.
def Parse.ensure (ok: Bool) (message: Text): {Parse t} () := if ok then () else Parse.fail message

--| Fails with `message` unless `ok`, reported at `at` rather than here: for a
--| check on something read since `at`, such as a number's size.
def Parse.ensureAt (at: Parse.Mark t) (ok: Bool) (message: Text): {Parse t} () :=
  if ok then ()
  else
    Parse.reset at
    Parse.fail message

--| The value in an `Option`, or fail with `message`.
def Parse.need (option: Option a) (message: Text): {Parse t} a := match option with
  | Some value => value
  | None => Parse.fail message

--| A `Fail` computation's value; its failure is a parse failure here:
--| `Parse.fromFail (() => word.toNatOrFail)`.
def Parse.fromFail (computation: () → {Fail} a): {Parse t} a := Fail.recover (message => Parse.fail message) computation

-- Pieces. Each reads a token or fails with what it expected.

--| The next item if `passes` holds for it, else "expected `what`".
def Parse.satisfy (what: Text) (passes: t → Bool): {Parse t} t := match Parse.next passes with
  | Some char => char
  | None => Parse.expected what

--| The next item's value if `select` gives one for it, else "expected `what`": a
--| token of a kind, read for what it carries.
--|
--|   Parse.one "a number" (match some | Num n => n)
def Parse.one (what: Text) (select: t → Option a): {Parse t} a :=
  let item := Parse.satisfy what (item => (select item).isSome)
  match select item with
    | Some value => value
    | None => Parse.expected what

--| The longest run of items that pass `passes`, at least one (a `NonEmptyList`), else
--| "expected `what`": `takeWhile1` for any items.
def Parse.span1 (what: Text) (passes: t → Bool): {Parse t} NonEmptyList t := match Parse.span passes with
  | [] => Parse.expected what
  | [first, ..rest] => [first, ..rest]

--| The end of the input, else "expected the end".
def Parse.end(): {Parse t} () := if Parse.mark().left == 0 then () else Parse.expected "the end"

--| The next item, without reading it: `None` at the end of the input. For
--| a parser that decides what to read by looking ahead
--| (`match Parse.peek() with …`); [`Parse.readsInPeek`] proves one.
def Parse.peek(): {Parse t} Option t := Parse.mark().rest.head

-- Choice and repetition. A failed alternative leaves the input as it was.

--| `Some` of `parser`'s value, or `None` with the input as it was if it
--| fails. Never fails.
def Parse.optional (parser: () → {Parse t} a): {Parse t} Option a := Parse.optionalFrom Parse.mark() parser

--| `optional` once it has marked where it started.
def Parse.optionalFrom (start: Parse.Mark t) (parser: () → {Parse t} a): {Parse t} Option a :=
  handle parser() with
    | return value => Some value
    | Parse.span passes, k => k (Parse.span passes)
    | Parse.next passes, k => k (Parse.next passes)
    | Parse.literal literal, k => k (Parse.literal literal)
    | Parse.mark u, k => k Parse.mark()
    | Parse.reset at, k => k (Parse.reset at)
    | Parse.note problem, k => k (Parse.note problem)
    | Parse.stop u, k =>
      Parse.reset start
      None
    | Parse.fatal message, k => Empty.absurd (Parse.fatal message)

--| The value found, else `fallback`'s.
def Parse.valueOr (found: Option a) (fallback: () → {Parse t} a): {Parse t} a := match found with
  | Some value => value
  | None => fallback()

--| The value of `first` if it succeeds, else of the first of the rest that does: `Parse.oneOf`'s loop.
def Parse.oneOfFrom (first: () → {Parse t} a): (rest: List (() → {Parse t} a)) → {Parse t} a
  | [] => first()
  | [next, ..rest] => Parse.valueOr (Parse.optional first) (() => Parse.oneOfFrom next rest)

--| The value of the first alternative that succeeds; if none does, the
--| failure that got furthest.
def Parse.oneOf (parsers: NonEmptyList (() → {Parse t} a)): {Parse t} a := Parse.oneOfFrom parsers.head parsers.tail

--| `parser` while it succeeds, at most `fuel` times, from `before`, the mark
--| at the start of the round. `found` is newest first.
-- The mark that ends a round (taken for the progress check) is the next
-- round's `before`, and also serves `optionalFrom`: nothing happens between
-- them, so `optional` and a fresh mark would each be an extra operation per
-- repetition.
def Parse.manyFrom (fuel: Nat) (parser: () → {Parse t} a) (found: List a) (before: Parse.Mark t): {Parse t} List a :=
  match fuel with
    | Zero => found.reverse
    | Succ more => Parse.manyRound more parser found before (Parse.optionalFrom before parser)

--| What `manyFrom` does with a round's `result` from `before`, with `more`
--| rounds left after it: stop if it failed, else go on from the mark that
--| shows it read something.
-- A function of its own so that proofs (Parse/Reads.sw) can name it. The
-- rest and the end are not closures passed in: that was two allocations a
-- round. `found.reverse` is computed only at the end: as a value it was
-- computed every round, quadratic in the rounds (AoC 2024 day 9's 20,000
-- digits: 0.6 s to 12 s, and 21 GB on the reference evaluator, SW-1055).
def Parse.manyRound (more: Nat) (parser: () → {Parse t} a) (found: List a) (before: Parse.Mark t) (result: Option a):
    {Parse t} List a :=
  match result with
    | None => found.reverse
    | Some value =>
      let after := Parse.mark()
      if after.offset > before.offset then Parse.manyFrom more parser [value, ..found] after
      else Empty.absurd (Parse.fatal "`many`: the parser matched without reading anything")

--| `parser`'s values while it succeeds, possibly none. Fails only if
--| `parser` succeeds without reading anything, which would repeat forever:
--| that stops the whole parse.
-- Every other round reads an item, so the items left are enough fuel.
def Parse.many (parser: () → {Parse t} a): {Parse t} List a :=
  let start := Parse.mark()
  Parse.manyFrom (start.left + 1) parser [] start

--| `parser`'s values, read from where each round starts for as long as items
--| are left; `found` is newest first, and `start` is the mark where this round
--| begins.
def Parse.manyToEndFrom (fuel: Nat) (what: Text) (parser: Parse.Mark t → {Parse t} a)
    (found: List a) (start: Parse.Mark t):
    {Parse t} List a :=
  match fuel, start.rest with
    | Succ more, [_, .._] =>
      let value := parser start
      let after := Parse.mark()
      if after.offset > start.offset then Parse.manyToEndFrom more what parser [value, ..found] after
      else Empty.absurd (Parse.fatal "`manyToEnd`: the parser matched without reading anything")
    | _, _ =>
      Parse.note (Expected what)
      found.reverse

--| `parser`'s values from one end of the input to the other, for a parser
--| that doesn't fail part-way, such as a lexer whose every character belongs
--| to some token: `parser` is given the mark where it starts, to choose by
--| what comes next, and the loop goes on while items are left. Unlike
--| `many` it installs no handler to back up from a failed round, so a round
--| costs one operation (the mark after it, which is the next round's start)
--| instead of three, and a failure of `parser` is a failure of the whole
--| parse here rather than the end of the repetition. At the end it notes
--| "expected `what`", as `many` does when its last try finds nothing. Fails
--| the whole parse, as `many` does, if a round reads nothing.
--|
--|   Parse.manyToEnd "a token" (start => lexeme start.rest)
def Parse.manyToEnd (what: Text) (parser: Parse.Mark t → {Parse t} a): {Parse t} List a :=
  let start := Parse.mark()
  Parse.manyToEndFrom (start.left + 1) what parser [] start

--| `step`'s values until it says stop, at most `fuel` rounds, from `before`,
--| the mark at the start of the round. `found` is newest first.
def Parse.loopFrom (fuel: Nat) (step: () → {Parse t} Option a) (found: List a) (before: Parse.Mark t):
    {Parse t} List a :=
  match fuel with
    | Zero => Empty.absurd (Parse.fatal "`loop`: the step went on without reading anything")
    | Succ more => Parse.loopRound more step found before (step())

--| What `loopFrom` does with a round's `result` from `before`, with `more`
--| rounds left after it: stop if the step said so, else go on from the mark
--| that shows it read something.
-- A function of its own so that proofs (Parse/Runs.sw) can name it.
def Parse.loopRound (more: Nat) (step: () → {Parse t} Option a) (found: List a)
    (before: Parse.Mark t) (result: Option a):
    {Parse t} List a :=
  match result with
    | None => found.reverse
    | Some value =>
      let after := Parse.mark()
      if after.offset > before.offset then Parse.loopFrom more step [value, ..found] after
      else Empty.absurd (Parse.fatal "`loop`: the step went on without reading anything")

--| `step`'s values, one round after another, until a round gives `None`:
--| the loop that hand-fuelled parsers write as `loop (fuel: Nat)`, with the
--| fuel taken from the input left. A round is `step()`, which decides by what
--| comes next: `None` to stop (it may read before it does), `Some value` to
--| go on, in which case it must have read at least one item since the round
--| began, or the whole parse stops (a `Some` that read nothing would repeat
--| forever). The step is also called when the input has ended, and must say
--| `None` there, having nothing to read. Unlike `many` it installs no handler:
--| a failure of `step` is a failure of the whole parse, and a round costs one
--| operation (the mark after it).
--|
--|   Parse.loop (() => if more() then Some (item()) else None)
-- Every round that goes on reads an item, so the items left plus one are
-- enough rounds: the last one sees the end of the input and stops.
def Parse.loop (step: () → {Parse t} Option a): {Parse t} List a :=
  let start := Parse.mark()
  Parse.loopFrom (start.left + 1) step [] start

--| `parser`'s values while it succeeds, at least one: a `NonEmptyList`.
def Parse.many1 (parser: () → {Parse t} a): {Parse t} NonEmptyList a :=
  let first := parser()
  NonEmptyList.cons first (Parse.many parser)

--| `parser` while it succeeds, at most `count` more times. `found` is newest first.
def Parse.repeatOptional (count: Nat) (parser: () → {Parse t} a) (found: List a): {Parse t} List a := match count with
  | Zero => found.reverse
  | Succ more =>
    Parse.onFound (Parse.optional parser) (value => Parse.repeatOptional more parser [value, ..found]) (() =>
      found.reverse)

--| `next` of what was found, else `done`.
-- A function of its own, not a `match` in the loops that use it, so that
-- proofs (Parse/Reads.sw) can name it.
def Parse.onFound (found: Option a) (next: a → {Parse t} b) (done: () → {Parse t} b): {Parse t} b := match found with
  | Some value => next value
  | None => done()

--| `parser` `count` times, failing as it fails, then at most `extra` more
--| times while it succeeds. `found` is newest first.
@[tailrec]
def Parse.repeatFrom (count extra: Nat) (parser: () → {Parse t} a) (found: List a): {Parse t} List a := match count with
  | Zero => Parse.repeatOptional extra parser found
  | Succ more =>
    let value := parser()
    Parse.repeatFrom more extra parser [value, ..found]

--| `parser`'s values, `atLeast` to `atMost` of them, as Megaparsec's `count'`:
--| the first `atLeast` must match, then it stops at the first failure or at
--| `atMost`. For exactly `count` values, [`Parse.exactly`] says so more
--| plainly: `exactly 3 digit` is three digits.
def Parse.repeat (atLeast atMost: Nat) (parser: () → {Parse t} a): {Parse t} List a :=
  Parse.repeatFrom atLeast (atMost - atLeast) parser []

--| `parser`'s values, exactly `count` of them: `Parse.exactly 3 Parse.digit`
--| reads three digits. Fails if `parser` does before the `count`th value.
def Parse.exactly (count: Nat) (parser: () → {Parse t} a): {Parse t} List a := Parse.repeat count count parser

--| `parser`, then `separator` and `parser` again as long as both match: at
--| least one value, so a `NonEmptyList`.
def Parse.sepBy1 (parser: () → {Parse t} a) (separator: () → {Parse t} ()): {Parse t} NonEmptyList a :=
  let first := parser()
  NonEmptyList.cons first
    (Parse.many (() =>
      separator()
      parser()))

--| What `sepBy` found as a list: the values, or none.
-- A function of its own so that proofs (Parse/Reads.sw) can name it.
def Parse.sepByValues: (found: Option (NonEmptyList a)) → List a
  | None => []
  | Some values => values.toList

--| `parser`, then `separator` and `parser` again as long as both match: any number of values, possibly none. Never fails.
def Parse.sepBy (parser: () → {Parse t} a) (separator: () → {Parse t} ()): {Parse t} List a :=
  Parse.sepByValues (Parse.optional (() => Parse.sepBy1 parser separator))

--| `first` combined with each operator and operand of `steps` in turn, from the left.
-- A function of its own so that proofs (Parse/Reads.sw) can name it.
def Parse.chainFold (first: a) (steps: List (a → a → a, a)): a :=
  steps.foldLeft first (left (combine, right) => combine left right)

--| `operand`, then `operator` and `operand` again as long as both match,
--| combined from the left (Parsec's `chainl1`). `operator` gives the function
--| that joins what is on its sides: with `operator` reading `+` as `(+)`,
--| `1+2+3` is `(1 + 2) + 3`. At least one operand; an operator without an
--| operand after it is left unread (the loop backs up to before the operator).
def Parse.chainLeft (operand: () → {Parse t} a) (operator: () → {Parse t} (a → a → a)): {Parse t} a :=
  let first := operand()
  let rest := Parse.many (() =>
    let combine := operator()
    let right := operand()
    (combine, right))
  Parse.chainFold first rest

--| How the operators of one level group: `a - b - c` is `(a - b) - c` for
--| `LeftAssociative`, `a ^ b ^ c` is `a ^ (b ^ c)` for `RightAssociative`.
type Parse.Associativity = | LeftAssociative | RightAssociative

--| One level of binary operators for `Parse.operators`: `operator` says, for
--| an item, whether it is an operator of this level and what it combines
--| its two sides into.
type Parse.Level (t: Type) (a: Type) = {
  associativity: Parse.Associativity,
  operator: t → Option (a → a → a)
}

--| The first level of the list, counting from `index`, that has an operator for `item`: its index,
--| associativity and combining function.
def Parse.operatorFrom (item: t) (index: Nat):
    (levels: List (Parse.Level t a)) → Option (Nat, Parse.Associativity, a → a → a)
  | [] => None
  | [level, ..rest] =>
    match level.operator item with
      | Some combine => Some (index, level.associativity, combine)
      | None => Parse.operatorFrom item (index + 1) rest

--| `operand` with the operators of `levels` between operands, grouped by
--| precedence: the first level binds loosest, so with levels `+` then `*`,
--| `1+2*3` is `1 + (2 * 3)`. Each operator is one item that a level's
--| `operator` accepts; a level chains as its associativity says. At least
--| one operand. An operator without an operand after it is left unread
--| (the parse backs up to before the operator), as `chainLeft` does.
--|
--| It is `Parse.chainLeft` once per level, each level's operand being the
--| next level's, with operators that read one item and expect `what`: the
--| same results and the same messages, "expected `what`" wherever no
--| operator was read, but a look at the next item per operand instead of
--| every level trying its operator under its own handler. A handler is
--| installed only where an operator is found.
--|
--|   Parse.operators "an operator" [
--|     { associativity = LeftAssociative, operator = plusOrMinus },
--|     { associativity = LeftAssociative, operator = times }
--|   ] term
def Parse.operators (what: Text) (levels: List (Parse.Level t a)) (operand: () → {Parse t} a): {Parse t} a :=
  Parse.operandsFrom (Parse.mark().left + 1) what levels levels.length operand 0

--| `Parse.operators` for operators of level `lowest` or tighter, with the
--| operand nested at most `depth` deep. Each nesting reads an operator, so
--| the items left are enough depth.
def Parse.operandsFrom (depth: Nat) (what: Text) (levels: List (Parse.Level t a)) (count: Nat)
    (operand: () → {Parse t} a) (lowest: Nat):
    {Parse t} a :=
  Parse.operandsAfter depth what levels count operand lowest (operand())

--| What `operandsFrom` does once it has read its `first` operand: the
--| operators of level `lowest` or tighter after it, if there is such a
--| level and depth left.
-- A function of its own, as `operatorsAfter` and `nextLowest` are, so that
-- proofs (Parse/RunsOperators.sw) can name it.
def Parse.operandsAfter (depth: Nat) (what: Text) (levels: List (Parse.Level t a)) (count: Nat)
    (operand: () → {Parse t} a) (lowest: Nat) (first: a):
    {Parse t} a :=
  match depth with
    | Succ inner if lowest < count =>
      Parse.operatorsFrom (Parse.mark().left + 1) inner what levels count operand lowest (count - 1) first
    -- Past the tightest level the operator after an operand is the caller's to try.
    | _ => first

--| The loosest level the right operand of an operator of `level` may hold
--| operators of: the next level for a left-associative operator, so that
--| `a - b - c` is `(a - b) - c`, and its own for a right-associative one.
def Parse.nextLowest (associativity: Parse.Associativity) (level: Nat): Nat := match associativity with
  | LeftAssociative => level + 1
  | RightAssociative => level

--| `left` followed by operators of level `lowest` to `highest` and their
--| operands, at most `fuel` of them. `highest` falls to the level of each
--| operator read: a tighter one after it would have been read by its right
--| operand. No operator there notes "expected `what`".
def Parse.operatorsFrom (fuel depth: Nat) (what: Text) (levels: List (Parse.Level t a)) (count: Nat)
    (operand: () → {Parse t} a) (lowest highest: Nat) (left: a):
    {Parse t} a :=
  match fuel, Parse.mark().rest with
    | Succ more, [item, .._] =>
      match Parse.operatorFrom item 0 levels with
        | Some (level, associativity, combine) if lowest <= level && level <= highest =>
          let right := Parse.optional (() =>
            let operator := Parse.next (item => True)
            Parse.operandsFrom depth what levels count operand (Parse.nextLowest associativity level))
          Parse.operatorsAfter more depth what levels count operand lowest level combine left right
        | _ =>
          Parse.note (Expected what)
          left
    | _, _ =>
      Parse.note (Expected what)
      left

--| What `operatorsFrom` does after an operator of `level` that `combine`s
--| its sides: with the `right` operand read, it goes on from the two
--| combined, for operators no tighter than `level`; with none, it gives
--| `left`, the operator left unread.
def Parse.operatorsAfter (more depth: Nat) (what: Text) (levels: List (Parse.Level t a)) (count: Nat)
    (operand: () → {Parse t} a) (lowest level: Nat) (combine: a → a → a) (left: a) (right: Option a):
    {Parse t} a :=
  match right with
    | Some right => Parse.operatorsFrom more depth what levels count operand lowest level (combine left right)
    | None => left

--| `parser`'s value and whether it read anything, or `None` with the input
--| as it was if it fails: `optional` with the progress check built in.
def Parse.attempt (parser: () → {Parse t} a): {Parse t} Option (a, Bool) := Parse.attemptFrom Parse.mark() parser

--| `attempt` once it has marked where it started.
def Parse.attemptFrom (start: Parse.Mark t) (parser: () → {Parse t} a): {Parse t} Option (a, Bool) :=
  handle parser() with
    | return value =>
      let finish := Parse.mark()
      let progressed: Bool := finish.offset > start.offset
      Some (value, progressed)
    | Parse.span passes, k => k (Parse.span passes)
    | Parse.next passes, k => k (Parse.next passes)
    | Parse.literal literal, k => k (Parse.literal literal)
    | Parse.mark u, k => k Parse.mark()
    | Parse.reset at, k => k (Parse.reset at)
    | Parse.note problem, k => k (Parse.note problem)
    | Parse.stop u, k =>
      Parse.reset start
      None
    | Parse.fatal message, k => Empty.absurd (Parse.fatal message)

--| `findAll`'s loop, at most `fuel` rounds: `skipNoise`, then `parser`, and
--| if that didn't read anything, one item skipped. `found` is newest
--| first.
def Parse.findAllFuel (fuel: Nat) (skipNoise: () → {Parse t} ()) (parser: () → {Parse t} a) (found: List a):
    {Parse t} List a :=
  match fuel with
    | Zero => found.reverse
    | Succ more =>
      skipNoise()
      match Parse.attempt parser with
        | Some (matched, progressed) =>
          let foundNow := [matched, ..found]
          if progressed then Parse.findAllFuel more skipNoise parser foundNow
          else
            Parse.onFound
              (Parse.next (char => True))
              (skipped => Parse.findAllFuel more skipNoise parser foundNow)
              (() => foundNow.reverse)
        | None =>
          Parse.onFound (Parse.next (char => True)) (skipped => Parse.findAllFuel more skipNoise parser found) (() =>
            found.reverse)

--| Every match of `parser` in the rest of the input, left to right, as Python's `re.findall`.
--| Matches don't overlap: where `parser` doesn't match, one item is
--| skipped, and the next try starts there. A match that reads nothing is
--| kept, and an item is skipped after it. Reads all of the input and
--| never fails.
def Parse.findAll (parser: () → {Parse t} a): {Parse t} List a :=
  Parse.findAllFuel (Parse.mark().left + 1) (() => ()) parser []

--| The values of `parser` everywhere it matches, as `Parse.findAll`, for a
--| `parser` that can match only where `starts` holds for the next item.
--| The items between are skipped with one `span`, not tried one at a
--| time. A match starting anywhere else is missed.
def Parse.findAllStarting (starts: t → Bool) (parser: () → {Parse t} a): {Parse t} List a :=
  let skipNoise := () =>
    let skipped := Parse.span (char => ¬(starts char))
    ()
  Parse.findAllFuel (Parse.mark().left + 1) skipNoise parser []

--| `parser`, but if it fails without getting past where it started, it
--| fails with "expected `what`" in place of what it expected there
--| (Megaparsec's `label`).
def Parse.label (what: Text) (parser: () → {Parse t} a): {Parse t} a := Parse.labelFrom what Parse.mark() parser

--| `label` once it has marked where it started.
def Parse.labelFrom (what: Text) (start: Parse.Mark t) (parser: () → {Parse t} a): {Parse t} a :=
  handle parser() with
    | return value =>
      if Parse.mark().offset == start.offset then Parse.note (Expected what) else ()
      value
    | Parse.span passes, k => k (Parse.span passes)
    | Parse.next passes, k => k (Parse.next passes)
    | Parse.literal literal, k => k (Parse.literal literal)
    | Parse.mark u, k => k Parse.mark()
    | Parse.reset at, k => k (Parse.reset at)
    | Parse.note problem, k => if Parse.mark().offset == start.offset then k () else k (Parse.note problem)
    | Parse.stop u, k =>
      Parse.reset start
      Parse.expected what
    | Parse.fatal message, k => Empty.absurd (Parse.fatal message)

--| `parser`, but any failure inside it becomes "expected `what`", for a short token that reads best as one thing.
--| It fails at the furthest point `parser` read to, dropping what it
--| expected inside, and backs up. Reported there, it outranks what is
--| expected nearer the start, as Megaparsec keeps the error that got
--| furthest. A blank line is such a token.
def Parse.labelWhole (what: Text) (parser: () → {Parse t} a): {Parse t} a :=
  let start := Parse.mark()
  Parse.labelWholeFrom what start parser start

--| The further on of `furthest` and where the parse is.
def Parse.further (furthest: Parse.Mark t): {Parse t} Parse.Mark t :=
  let here := Parse.mark()
  if here.offset > furthest.offset then here else furthest

--| `labelWhole` once it has marked where it started, given the furthest
--| point read to so far.
-- A function of its own so that proofs (Parse/Reads.sw) can name it.
def Parse.labelWholeFrom (what: Text) (start: Parse.Mark t) (parser: () → {Parse t} a):
    (furthest: Parse.Mark t) → {Parse t} a :=
  handle parser() with
    | return value => furthest => value
    | Parse.span passes, k => furthest =>
      let read := Parse.span passes
      k read (Parse.further furthest)
    | Parse.next passes, k => furthest =>
      let read := Parse.next passes
      k read (Parse.further furthest)
    | Parse.literal literal, k => furthest =>
      let read := Parse.literal literal
      k read (Parse.further furthest)
    | Parse.mark u, k => furthest => k Parse.mark() furthest
    | Parse.reset at, k => furthest =>
      Parse.reset at
      k () furthest
    | Parse.note problem, k => furthest => k () furthest
    | Parse.stop u, k => furthest =>
      Parse.reset furthest
      Parse.note (Expected what)
      Parse.reset start
      Empty.absurd Parse.stop()
    | Parse.fatal message, k => furthest => Empty.absurd (Parse.fatal message)

--| `body` with `self` for its nested parser, at most `fuel` levels deep.
def Parse.recursiveFuel (fuel: Nat) (body: (() → {Parse t} a) → {Parse t} a): {Parse t} a := match fuel with
  | Zero => Empty.absurd (Parse.fatal "`recursive`: the parser called itself without reading anything")
  | Succ more => body (() => Parse.recursiveFuel more body)

--| A parser for nested input: `body` gets the parser being defined, to call
--| for the nested parts. Fails only as `body` does, or if it nests without
--| reading anything between levels (left recursion), which would recurse
--| forever: that stops the whole parse.
-- Every other level reads an item, so the items left are enough fuel.
def Parse.recursive (body: (() → {Parse t} a) → {Parse t} a): {Parse t} a :=
  Parse.recursiveFuel (Parse.mark().left + 1) body

--| `Parse.recursiveFuel` for a parser that takes an argument.
def Parse.recursiveWithFuel (fuel: Nat) (body: (b → {Parse t} a) → b → {Parse t} a) (argument: b): {Parse t} a :=
  match fuel with
    | Zero => Empty.absurd (Parse.fatal "`recursiveWith`: the parser called itself without reading anything")
    | Succ more => body (inner => Parse.recursiveWithFuel more body inner) argument

--| `Parse.recursive` for a parser that takes an argument, such as the
--| layout a nested part is read at: `body` gets the parser being defined,
--| `b → {Parse t} a`, to call for the nested parts with the argument they
--| need, and the parser starts with `argument`. Fails only as `body` does,
--| or if it nests without reading anything between levels, which stops the
--| whole parse.
--|
--|   Parse.recursiveWith (nested depth => … nested (depth + 1) …) 0
-- Every other level reads an item, so the items left are enough fuel.
def Parse.recursiveWith (body: (b → {Parse t} a) → b → {Parse t} a) (argument: b): {Parse t} a :=
  Parse.recursiveWithFuel (Parse.mark().left + 1) body argument

-- Runners. The parser must read all of its input; errors give the line and
-- column, counted from 1.

--| `parser`, then the end.
def Parse.whole (chars: List t) (parser: () → {Parse t} a): Result a Parse.Failure := Parse.run chars (() =>
  let value := parser()
  Parse.end()
  value)

-- What the handler does with each operation followed by the rest of the
-- parser `k`. Each holds by `byComputing`, or one `rewrite`.

theorem Parse.runFromPure ∀ (state: Parse.State t) (value: a): Parse.runFrom state (() => value) = Ok value :=
  byComputing

theorem Parse.runFromMark ∀ (state: Parse.State t) (k: Parse.Mark t → {Parse t} a):
    Parse.runFrom state (() => k Parse.mark()) = Parse.runFrom state (() => k state.at) :=
  byComputing

theorem Parse.runFromReset ∀ (state: Parse.State t) (at: Parse.Mark t) (k: () → {Parse t} a):
    Parse.runFrom state (() => k (Parse.reset at)) = Parse.runFrom { state | at } (() => k ()) :=
  byComputing

theorem Parse.runFromNote ∀ (state: Parse.State t) (problem: Parse.Problem) (k: () → {Parse t} a):
    Parse.runFrom state (() => k (Parse.note problem)) = Parse.runFrom (state.note problem) (() => k ()) :=
  byComputing

theorem Parse.runFromStop ∀ (state: Parse.State t) (k: Empty → {Parse t} a):
    Parse.runFrom state (() => k Parse.stop()) = Err state.failure :=
  byComputing

theorem Parse.runFromFatal ∀ (state: Parse.State t) (message: Text) (k: Empty → {Parse t} a):
    Parse.runFrom state (() => k (Parse.fatal message))
      = Err { offset = state.at.offset, messages = [message], expected = [], width = 0 } :=
  byComputing

--| `next`: the handler's step, as `Parse.State.next` gives it.
theorem Parse.runFromNext ∀ (state: Parse.State t) (passes: t → Bool) (k: Option t → {Parse t} a):
    Parse.runFrom state (() => k (Parse.next passes))
      = Parse.runFrom (state.next passes).snd (() => k (state.next passes).fst) :=
  match starts: state.at.rest with
    | [] => byComputing
    | [char, ..after] =>
      match holds: passes char with
        | True | False => byComputing

--| `literal`: the handler's step, as `Parse.State.literal` gives it.
theorem Parse.runFromLiteral ∀ (state: Parse.State t) (literal: Parse.Literal t) (k: Bool → {Parse t} a):
    Parse.runFrom state (() => k (Parse.literal literal))
      = Parse.runFrom (state.literal literal).snd (() => k (state.literal literal).fst) :=
  match stripped: List.stripPrefixBy state.at.rest literal.items literal.same with | None | Some _ => byComputing

theorem Parse.runFromSpan ∀ (state: Parse.State t) (passes: t → Bool) (k: List t → {Parse t} a):
    Parse.runFrom state (() => k (Parse.span passes))
      = Parse.runFrom (state.advance (state.at.rest.span passes).snd (state.at.rest.span passes).fst.length) (() =>
        k (state.at.rest.span passes).fst) :=
  byComputing

--| `literal` where the input starts with its items: it reads them, when `same`
--| holds of each item and itself.
theorem Parse.runFromLiteralThere ∀ (state: Parse.State t) (literal: Parse.Literal t)
    (rest: List t) (k: Bool → {Parse t} a)
    (reflexive: ∀ (x: t) => literal.same x x = True)
    (starts: state.at.rest = List.append literal.items rest):
    Parse.runFrom state (() => k (Parse.literal literal))
      = Parse.runFrom (state.advance rest literal.items.length) (() => k True) :=
  rewrite starts, List.stripPrefixByAppend literal.same reflexive literal.items rest

--| `span` where the input starts with `taken`, all passing, and the item
--| after them (if any) doesn't: it reads `taken`.
theorem Parse.runFromSpanThere ∀ (state: Parse.State t) (passes: t → Bool)
    (taken rest: List t) (k: List t → {Parse t} a)
    (starts: state.at.rest = List.append taken rest)
    (all: List.all taken passes = True)
    (stops: List.takeWhile rest passes = []):
    Parse.runFrom state (() => k (Parse.span passes))
      = Parse.runFrom (state.advance rest taken.length) (() => k taken) :=
  rewrite Parse.runFromSpan state passes k, starts, List.spanAppend passes taken rest all stops

--| `next` where the next item passes: it reads it.
theorem Parse.runFromNextThere ∀ (state: Parse.State t) (passes: t → Bool) (char: t)
    (rest: List t) (k: Option t → {Parse t} a)
    (starts: state.at.rest = [char, ..rest])
    (holds: passes char = True):
    Parse.runFrom state (() => k (Parse.next passes)) = Parse.runFrom (state.advance rest 1) (() => k (Some char)) :=
  rewrite starts, holds

theorem Parse.runFromEndThere ∀ (state: Parse.State t) (k: () → {Parse t} a)
    (atEnd: state.at.left = 0):
    Parse.runFrom state (() => k (Parse.end())) = Parse.runFrom state (() => k ()) :=
  rewrite atEnd

-- `optional` marks where it starts, then runs the parser under
-- `optionalFrom`, which passes each reading operation on, gives `Some` of a
-- value, and backs up to the mark on a failure. So a run of `optional
-- parser` follows the parser's own operations.

theorem Parse.runFromOptional ∀ (state: Parse.State t) (parser: () → {Parse t} a) (k: Option a → {Parse t} b):
    Parse.runFrom state (() => k (Parse.optional parser))
      = Parse.runFrom state (() => k (Parse.optionalFrom state.at parser)) :=
  byComputing

theorem Parse.runFromOptionalFromSpan ∀ (state: Parse.State t) (start: Parse.Mark t) (passes: t → Bool)
    (rest: List t → {Parse t} a) (k: Option a → {Parse t} b):
    Parse.runFrom state (() => k (Parse.optionalFrom start (() => rest (Parse.span passes))))
      = Parse.runFrom state (() =>
        let taken := Parse.span passes
        k (Parse.optionalFrom start (() => rest taken))) :=
  byComputing

theorem Parse.runFromOptionalFromNext ∀ (state: Parse.State t) (start: Parse.Mark t) (passes: t → Bool)
    (rest: Option t → {Parse t} a) (k: Option a → {Parse t} b):
    Parse.runFrom state (() => k (Parse.optionalFrom start (() => rest (Parse.next passes))))
      = Parse.runFrom state (() =>
        let found := Parse.next passes
        k (Parse.optionalFrom start (() => rest found))) :=
  byComputing

theorem Parse.runFromOptionalFromLiteral ∀ (state: Parse.State t) (start: Parse.Mark t) (literal: Parse.Literal t)
    (rest: Bool → {Parse t} a) (k: Option a → {Parse t} b):
    Parse.runFrom state (() => k (Parse.optionalFrom start (() => rest (Parse.literal literal))))
      = Parse.runFrom state (() =>
        let found := Parse.literal literal
        k (Parse.optionalFrom start (() => rest found))) :=
  byComputing

--| Success: the parser has given a value.
theorem Parse.runFromOptionalFromPure ∀ (state: Parse.State t) (start: Parse.Mark t)
    (value: a) (k: Option a → {Parse t} b):
    Parse.runFrom state (() => k (Parse.optionalFrom start (() => value)))
      = Parse.runFrom state (() => k (Some value)) :=
  byComputing

--| Backtracking: the parser has failed, so the input is as it was at the mark.
theorem Parse.runFromOptionalFromStop ∀ (state: Parse.State t) (start: Parse.Mark t)
    (rest: Empty → {Parse t} a) (k: Option a → {Parse t} b):
    Parse.runFrom state (() => k (Parse.optionalFrom start (() => rest Parse.stop())))
      = Parse.runFrom { state | at = start } (() => k None) :=
  byComputing

--| `oneOf` with an alternative after `first`: if `optional first` succeeds,
--| whatever follows it, `first`'s value; if it backs up, the rest.
theorem Parse.runFromOneOfFromSome ∀ (state after: Parse.State t) (first next: () → {Parse t} a)
    (rest: List (() → {Parse t} a)) (value: a) (k: a → {Parse t} b)
    (succeeds: ∀ (choose: Option a → {Parse t} a) (finish: a → {Parse t} b) => Parse.runFrom state (() =>
      finish (choose (Parse.optional first)))
      = Parse.runFrom after (() => finish (choose (Some value)))):
    Parse.runFrom state (() => k (Parse.oneOfFrom first [next, ..rest])) = Parse.runFrom after (() => k value) :=
  succeeds (found => Parse.valueOr found (() => Parse.oneOfFrom next rest)) k

theorem Parse.runFromOneOfFromNone ∀ (state after: Parse.State t) (first next: () → {Parse t} a)
    (rest: List (() → {Parse t} a)) (k: a → {Parse t} b)
    (fails: ∀ (choose: Option a → {Parse t} a) (finish: a → {Parse t} b) => Parse.runFrom state (() =>
      finish (choose (Parse.optional first)))
      = Parse.runFrom after (() => finish (choose None))):
    Parse.runFrom state (() => k (Parse.oneOfFrom first [next, ..rest]))
      = Parse.runFrom after (() => k (Parse.oneOfFrom next rest)) :=
  fails (found => Parse.valueOr found (() => Parse.oneOfFrom next rest)) k

--| The last alternative is run as it is.
theorem Parse.runFromOneOfFromLast ∀ (state: Parse.State t) (only: () → {Parse t} a) (k: a → {Parse t} b):
    Parse.runFrom state (() => k (Parse.oneOfFrom only [])) = Parse.runFrom state (() => k (only())) :=
  byComputing

theorem Parse.runPure ∀ (input: List t) (value: a): Parse.run input (() => value) = Ok value := byComputing
