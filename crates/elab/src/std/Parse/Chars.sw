import Parse.Associativity (LeftAssociative, RightAssociative)
import Parse.Problem (Expected, Literal, Literals, Message)

-- The pieces that read text, `{Parse Char}`: characters, digits, numbers,
-- words, spaces and lines, and the runners that take a `Text`. The
-- operations and combinators they are built from are generic, in Parse.sw.

--| The character `expected`, else "expected 'c'".
def Parse.char (expected: Char): {Parse Char} () :=
  let char := Parse.satisfy "'${expected}'" (== expected)
  ()

--| The text `expected`, else "expected 'text'".
def Parse.text (expected: Text): {Parse Char} () :=
  if Parse.literal { items = expected.toList, same = Text.sameChar } then ()
  else
    Parse.note (Literal expected)
    Empty.absurd Parse.stop()

--| The longest run of characters for which `passes` holds, possibly empty. Never fails.
def Parse.takeWhile (passes: Char → Bool): {Parse Char} Text := Parse.span passes |> Text.fromList

--| The longest run of characters for which `passes` holds, at least one, else
--| "expected `what`".
def Parse.takeWhile1 (what: Text) (passes: Char → Bool): {Parse Char} Text := match Parse.span passes with
  | [] => Parse.expected what
  | chars => Text.fromList chars

--| Whether a character is an ASCII digit, `0` to `9`.
def Parse.isDigit (char: Char): Bool := char.isAsciiDigit

--| Whether a character is a space or a tab.
def Parse.isSpace (char: Char): Bool := char == ' ' ∨ char == '\t'

--| A whole number written in decimal digits, else "expected a number".
def Parse.nat(): {Parse Char} Nat := match Parse.span Parse.isDigit with
  | [] => Parse.expected "a number"
  | digits => digits.map (digit => digit.digitValue.getOrElse 0) |> Nat.fromDigits

--| A whole number of `atLeast` to `atMost` decimal digits (at least one).
--| Otherwise it fails with "expected a number of 1 to 3 digits", or "expected
--| a 2-digit number", where the number starts. All the digits there are read
--| first, so "1234" is too long, not 123 and a 4.
def Parse.natDigits (atLeast atMost: Nat): {Parse Char} Nat :=
  let start := Parse.mark()
  let digits := Parse.span Parse.isDigit
  let count := digits.length
  if 0 < count ∧ atLeast ≤ count ≤ atMost then digits.map (digit => digit.digitValue.getOrElse 0) |> Nat.fromDigits
  else
    Parse.reset start
    let fewest := if atLeast == 0 then 1 else atLeast
    Parse.expected
      (if fewest == atMost then "a ${atMost}-digit number" else "a number of ${fewest} to ${atMost} digits")

--| A whole number with an optional '+' or '-' in front, else "expected a
--| number". A leading '+' is accepted like a '-', so a stray '+' before a
--| number is read as its sign: an expression parser reading "1 + +2" sees the
--| second '+' as the start of 2, not as another operator.
def Parse.int(): {Parse Char} Int :=
  if Parse.literal { items = ['-'], same = Text.sameChar } then -(Parse.nat().toInt)
  else if Parse.literal { items = ['+'], same = Text.sameChar } then Parse.nat().toInt
  else Parse.nat().toInt

--| One decimal digit, else "expected a digit".
def Parse.digit(): {Parse Char} Fin 10 :=
  let char := Parse.satisfy "a digit" Parse.isDigit
  Parse.need char.toDigit "expected a digit"

--| Spaces and tabs, possibly none. Never fails.
def Parse.spaces(): {Parse Char} () :=
  let skipped := Parse.span Parse.isSpace
  ()

--| Spaces and tabs, at least one, else "expected a space".
def Parse.spaces1(): {Parse Char} () :=
  let skipped := Parse.takeWhile1 "a space" Parse.isSpace
  ()

--| `parser` with spaces and tabs allowed around it: `token nat` reads " 12 ".
def Parse.token (parser: () → {Parse Char} a): {Parse Char} a :=
  Parse.spaces()
  let value := parser()
  Parse.spaces()
  value

--| Reads `suffix`, else "expected 'suffix'", then gives `value`: Lean's
--| `value <* string suffix`. Meant for `|>`, which runs its left side first
--| (docs/syntax.md, "Effectful code"), so the value's own parsers have read
--| their part before `suffix` is read:
--| `Mul (text "mul("; nat()) (char ','; nat()) |> before ")"`.
def Parse.before (value: a) (suffix: Text): {Parse Char} a :=
  Parse.text suffix
  value

--| A line break, "\n" or "\r\n", else "expected a line break".
def Parse.newline(): {Parse Char} () :=
  if Parse.literal { items = ['\n'], same = Text.sameChar } then ()
  else if Parse.literal { items = ['\r', '\n'], same = Text.sameChar } then ()
  else Parse.expected "a line break"

--| A line break or the end of the input, else "expected the end of the line".
def Parse.lineEnd(): {Parse Char} () :=
  if Parse.mark().left == 0 then ()
  else if Parse.literal { items = ['\n'], same = Text.sameChar } then ()
  else if Parse.literal { items = ['\r', '\n'], same = Text.sameChar } then ()
  else Parse.expected "the end of the line"

--| A line break, a line of nothing but spaces and tabs, and its line break;
--| else "expected a blank line" where it starts.
def Parse.blankLine(): {Parse Char} () := Parse.labelWhole "a blank line" (() =>
  Parse.newline()
  Parse.spaces()
  Parse.newline())

--| The value paired with the first word that comes next, as aoc-parse's
--| `{ "L" => …, "R" => … }`; else "expected 'L' or 'R'". Words are tried in
--| order, so put a word before any that start it.
def Parse.pick (choices: List (Text, a)): {Parse Char} a :=
  match choices.find (choice => Parse.literal { items = choice.fst.toList, same = Text.sameChar }) with
    | Some (word, value) => value
    | None =>
      Parse.noteWords choices
      Empty.absurd Parse.stop()

--| Notes each word of `pick`'s choices as expected here, in one operation.
def Parse.noteWords: (words: List (Text, a)) → {Parse Char} ()
  | [] => ()
  | words => Parse.note (Literals (words.map (choice => choice.fst)))

--| One `parser` per line, at least one (a `NonEmptyList`). The line break after
--| the last is left for what comes next.
def Parse.lines (parser: () → {Parse Char} a): {Parse Char} NonEmptyList a := Parse.sepBy1 parser Parse.newline

--| Blocks separated by a blank line, at least one (a `NonEmptyList`): `sections (() => lines nat)`.
def Parse.sections (parser: () → {Parse Char} a): {Parse Char} NonEmptyList a := Parse.sepBy1 parser Parse.blankLine

--| `parser` on a line after the first of a `section`. If it fails, a blank
--| line before this line is also expected there: the section may have ended.
--| Where the line starts, that is a blank line, as `blankLine` expects there.
def Parse.sectionLine (parser: () → {Parse Char} a): {Parse Char} a := Parse.sectionLineFrom Parse.mark() parser

--| `sectionLine` once it has marked where the line starts.
-- A function of its own so that proofs (Parse/Reads.sw) can name it.
def Parse.sectionLineFrom (start: Parse.Mark Char) (parser: () → {Parse Char} a): {Parse Char} a :=
  handle parser() with
    | return value => value
    | Parse.span passes, k => k (Parse.span passes)
    | Parse.next passes, k => k (Parse.next passes)
    | Parse.literal literal, k => k (Parse.literal literal)
    | Parse.mark u, k => k Parse.mark()
    | Parse.reset at, k => k (Parse.reset at)
    | Parse.note problem, k => k (Parse.note problem)
    | Parse.stop u, k =>
      let here := Parse.mark()
      Parse.note (Expected (if here.offset == start.offset then "a blank line" else "a blank line before this line"))
      Empty.absurd Parse.stop()
    | Parse.fatal message, k => Empty.absurd (Parse.fatal message)

--| One `parser` per line, at least one (a `NonEmptyList`), then a blank line: a section that
--| another follows, as aoc-parse's `section`. For input whose sections hold
--| different things: `section rule`, then `lines update` for the last. If a
--| line after the first fails, a blank line before it is expected too.
def Parse.section (parser: () → {Parse Char} a): {Parse Char} NonEmptyList a :=
  let first := parser()
  let rest := Parse.many (() =>
    Parse.newline()
    Parse.sectionLine parser)
  Parse.blankLine()
  NonEmptyList.cons first rest

--| Rows of cells, one row per line, at least one cell in each, so a
--| `NonEmptyList` of `NonEmptyList`s. Rows may differ in length.
def Parse.grid (cell: () → {Parse Char} a): {Parse Char} NonEmptyList (NonEmptyList a) :=
  Parse.lines (() => Parse.many1 cell)

--| One row of `looseGrid`: its cells and its line break, if any. Fails without
--| a problem of its own at the end of the input, where there is no row.
def Parse.looseRow (cell: () → {Parse Char} a): {Parse Char} List a :=
  if Parse.mark().left == 0 then Empty.absurd Parse.stop()
  else
    let cells := Parse.many cell
    Parse.lineEnd()
    cells

--| Rows of cells, one row per line, as `grid`, but possibly no rows, and a
--| row may have no cells: every line, empty or not, is a row. Never fails
--| at the start of a line; a bad cell is "expected '@', '.' or the end of
--| the line".
def Parse.looseGrid (cell: () → {Parse Char} a): {Parse Char} List (List a) := Parse.many (() => Parse.looseRow cell)

--| The line and column of the character `offset` characters into `chars`.
def Parse.lineAndColumn (chars: List Char) (offset: Nat): (Nat, Nat) :=
  let before := chars.take offset
  let column := before.reverse.takeWhile (≠ '\n') |> .length
  (before.count (== '\n') + 1, column + 1)

--| What `failure` expected, in words for a runner whose input ends with `endOfInput`.
--| "a line break" and "the end" together are "the end of the line", since
--| either ends it.
def Parse.Failure.expectations (failure: Parse.Failure) (endOfInput: Text): List Text :=
  let endsLine := failure.expected.any (== "a line break") ∧ failure.expected.any (== "the end")
  failure.expected
    |> .filter (what => ¬(endsLine ∧ what == "the end"))
    |> .map (what =>
      if endsLine ∧ what == "a line break" then "the end of the line"
      else if what == "the end" then endOfInput
      else what)
    |> .uniqueDecEq

--| What was found `failure.offset` characters into `chars`, for "got 'x'".
--| It is as many characters as the longest text expected there, up to a line
--| break, as Megaparsec shows, then on to the end of a word they stop in;
--| a line break is `lineBreak`, and past the last character is
--| `endOfInput`.
def Parse.Failure.found (failure: Parse.Failure) (chars: List Char) (endOfInput lineBreak: Text): Text :=
  let rest := chars.drop failure.offset
  match rest with
    | [] => endOfInput
    | [char, ..after] =>
      if char == '\n' ∨ char == '\r' then lineBreak
      else if failure.width > 1 then
        let head := rest.take failure.width |> .takeWhile (shownChar => shownChar ≠ '\n' ∧ shownChar ≠ '\r')
        let endsInWord := head.length == failure.width ∧ head.last.any Char.isAsciiAlphanumeric
        let tail := if endsInWord then rest.drop failure.width |> .takeWhile Char.isAsciiAlphanumeric else []
        "'${Text.fromList (head ++ tail)}'"
      else if char == '\t' then "a tab"
      else "'${char}'"

--| The texts as an English list, with " or " before the last and ", "
--| between the rest: `["a", "b", "c"]` is `"a, b or c"`. One text is
--| unchanged, and two are joined with " or ".
def Parse.joinOr: (items: List Text) → Text
  | [] => ""
  | [only] => only
  | [first, second] => "${first} or ${second}"
  | [first, ..rest] => "${first}, ${Parse.joinOr rest}"

--| `failure` as one message: the parser's own messages, then "expected A,
--| B or C, got 'x'" with what was found in `chars` instead. `endOfInput` and
--| `lineBreak` name the end of `chars` and a line break in it.
def Parse.Failure.describe (failure: Parse.Failure) (chars: List Char) (endOfInput lineBreak: Text): Text :=
  let expectations := failure.expectations endOfInput
  let expectedPart :=
    if expectations == [] then []
    else ["expected ${Parse.joinOr expectations}, got ${failure.found chars endOfInput lineBreak}"]
  match failure.messages ++ expectedPart with
    | [] => "the parser failed"
    | [only] => only
    | parts => Text.joinWith parts "; "

--| `parser` on all of `input`, else fail with "line 3, column 5: expected
--| ',', got ';'". For input with sections; holds the input as a list of
--| characters, so for large line-per-record input `Parse.eachLine` is faster
--| and smaller. Line breaks at the end of the input are allowed.
def Parse.all (input: Text) (parser: () → {Parse Char} a): {Fail} a :=
  let chars := input.toList
  match Parse.whole chars (() => Parse.withFinalLineBreaks parser) with
    | Ok value => value
    | Err failure => Fail.fail (Parse.allMessage chars failure)

--| Fails after the first line break from `start`, with a message of its own
--| for `Parse.all`: a failure the parser's own attempt to go on got further
--| than is reported instead.
def Parse.extraBlankLine (start: Parse.Mark Char): {Parse Char} () :=
  (Parse.reset start; Parse.newline(); Parse.note (Message "expected the end of the input, got a blank line"))
  Empty.absurd Parse.stop()

--| `parser`, then any line breaks at the end of the input; if there are none,
--| a line break is expected there too, for the message. One line break is
--| allowed before more input; a further one fails after it, as "got a blank
--| line", unless the parser's own attempt to go on got further.
def Parse.withFinalLineBreaks (parser: () → {Parse Char} a): {Parse Char} a :=
  let value := parser()
  let start := Parse.mark()
  let finalLineBreaks := Parse.span (char => char == '\n' ∨ char == '\r')
  if finalLineBreaks == [] then Parse.note (Expected "a line break")
  else if finalLineBreaks == ['\n'] then ()
  else if finalLineBreaks == ['\r', '\n'] then ()
  else if start.left == finalLineBreaks.length then ()
  else Parse.extraBlankLine start
  value

--| `Parse.all`'s message for `failure`.
def Parse.allMessage (chars: List Char) (failure: Parse.Failure): Text :=
  let (line, column) := Parse.lineAndColumn chars failure.offset
  "line ${line}, column ${column}: ${failure.describe chars "the end of the input" "the end of the line"}"

--| `parser` on one line, else fail with "column 5: expected ',', got ';'".
--| One line break at the end is allowed; a failure after a line break gives
--| its line too, as `Parse.all` does.
def Parse.line (line: Text) (parser: () → {Parse Char} a): {Fail} a :=
  let chars := line.toList
  match Parse.whole chars (() => Parse.withFinalLineBreak parser) with
    | Ok value => value
    | Err failure => Fail.fail (Parse.lineMessage chars failure)

--| `parser`, then a line break if there is one.
def Parse.withFinalLineBreak (parser: () → {Parse Char} a): {Parse Char} a :=
  let value := parser()
  let finalLineBreak := Parse.optional Parse.newline
  value

--| `Parse.line`'s message for `failure`: the column, and the line too if
--| it is past a line break.
def Parse.lineMessage (chars: List Char) (failure: Parse.Failure): Text :=
  match Parse.lineAndColumn chars failure.offset with
    | (1, column) => "column ${column}: ${failure.describe chars "the end of the line" "a line break"}"
    | (lineNumber, column) =>
      "line ${lineNumber}, column ${column}: ${failure.describe chars "the end of the input" "a line break"}"

--| `parser` on each line of `input`, split as `Text.lines` splits, else fail
--| with "line 3, column 5: expected ',', got ';'" for the first line that
--| fails. Lines are numbered from 1.
def Parse.eachLine (input: Text) (parser: () → {Parse Char} a): {Fail} List a := input.lines.withIndex.map (((index,
  line)) =>
  let chars := line.toList
  match Parse.whole chars parser with
    | Ok value => value
    | Err failure =>
      Fail.fail
        "line ${index + 1}, column ${failure.offset + 1}: ${failure.describe chars "the end of the line" "a line break"}")

-- What each piece does where the input has what it reads. Each holds by
-- `rewrite` and `byComputing`.

theorem Parse.runFromTextThere ∀ (state: Parse.State Char) (expected: Text) (rest: List Char) (k: () → {Parse Char} a)
    (starts: state.at.rest = List.append expected.toList rest):
    Parse.runFrom state (() => k (Parse.text expected))
      = Parse.runFrom (state.advance rest expected.toList.length) (() => k ()) :=
  rewrite starts, List.stripPrefixByAppend Text.sameChar Text.sameCharRefl expected.toList rest

theorem Parse.sameChar ∀ (char: Char): (char == char) = True := DecEq.refl char

--| `Text.sameChar` holds only of equal characters.
theorem Parse.sameCharExact ∀ (x y: Char) (same: Text.sameChar x y = True): x = y := Char.ext x y same.read

--| `Parse.literal` on characters strips its items as `Text.stripPrefixChars` does.
theorem Parse.stripPrefixBySameChar ∀ (input prefix: List Char):
    List.stripPrefixBy input prefix Text.sameChar = Text.stripPrefixChars prefix input :=
  match input, prefix with
    | input, [] => byComputing
    | [], [p, ..ps] => byComputing
    | [x, ..more], [p, ..ps] =>
      let byIf := (b: Bool) => if b then List.stripPrefixBy more ps Text.sameChar else None
      let charsIf := (b: Bool) => if b then Text.stripPrefixChars ps more else None
      match same: Text.sameChar p x with
        | True => Parse.stripPrefixBySameChar more ps
        | False => Eq.trans (Eq.cong byIf same) (Eq.cong charsIf same).flipped

theorem Parse.runFromCharThere ∀ (state: Parse.State Char) (expected: Char) (rest: List Char) (k: () → {Parse Char} a)
    (starts: state.at.rest = [expected, ..rest]):
    Parse.runFrom state (() => k (Parse.char expected)) = Parse.runFrom (state.advance rest 1) (() => k ()) :=
  rewrite starts, Parse.sameChar expected

--| `nat` on a run of digits, followed by something else or nothing.
theorem Parse.runFromNatThere ∀ (state: Parse.State Char) (digits rest: List Char) (k: Nat → {Parse Char} a)
    (starts: state.at.rest = List.append digits rest)
    (some: digits ≠ [])
    (all: List.all digits Parse.isDigit = True)
    (stops: List.takeWhile rest Parse.isDigit = []):
    Parse.runFrom state (() => k (Parse.nat()))
      = Parse.runFrom (state.advance rest digits.length) (() =>
        k (digits.map (digit => digit.digitValue.getOrElse 0) |> Nat.fromDigits)) :=
  match digits with
    | [] => (some byComputing).impossible
    | [first, ..others] => rewrite starts, List.spanAppend Parse.isDigit [first, ..others] rest all stops

--| `optional (text expected)` from a state where `expected` comes next reads it and goes on with `Some ()`.
theorem Parse.runFromOptionalTextThere ∀ (state: Parse.State Char) (expected: Text)
    (rest: List Char) (k: Option () → {Parse Char} a)
    (starts: state.at.rest = List.append expected.toList rest):
    Parse.runFrom state (() => k (Parse.optional (() => Parse.text expected)))
      = Parse.runFrom (state.advance rest expected.toList.length) (() => k (Some ())) :=
  rewrite starts, List.stripPrefixByAppend Text.sameChar Text.sameCharRefl expected.toList rest

theorem Parse.runFromOptionalTextNotThere ∀ (state: Parse.State Char) (expected: Text) (k: Option () → {Parse Char} a)
    (absent: Text.stripPrefixChars expected.toList state.at.rest = None):
    Parse.runFrom state (() => k (Parse.optional (() => Parse.text expected)))
      = Parse.runFrom { state.note (Literal expected) | at = state.at } (() => k None) :=
  rewrite Parse.stripPrefixBySameChar state.at.rest expected.toList, absent

--| With concrete alternatives the run computes: the first of two words.
theorem Parse.runFromOneOfExample ∀ (state: Parse.State Char) (rest: List Char) (k: Nat → {Parse Char} b)
    (starts: state.at.rest = List.append "ab".toList rest):
    Parse.runFrom state (() =>
      k
        (Parse.oneOf [
          () =>
            Parse.text "ab"
            1,
          () =>
            Parse.text "cd"
            2
        ]))
      = Parse.runFrom (state.advance rest 2) (() => k 1) :=
  rewrite starts

theorem Parse.runFail ∀ (message: Text):
    Parse.run ([]: List Char) (() => (Parse.fail message: Nat))
      = Err { offset = 0, messages = [message], expected = [], width = 0 } :=
  byComputing

-- Tests. Each runs a parser with `Parse.line` (errors give the column) or
-- `Parse.all` (the line and column).

--| The value of `parser` on `line`, or the error, with its column.
def Parse.Tests.lineResult (line: Text) (parser: () → {Parse Char} a): Result a Text :=
  Fail.toResult (() => Parse.line line parser)

--| The value of `parser` on the whole input, or the error, with its line and column.
def Parse.Tests.allResult (input: Text) (parser: () → {Parse Char} a): Result a Text :=
  Fail.toResult (() => Parse.all input parser)

--| The error if `parser` fails on `line`, else "": for parsers whose value is `()`.
def Parse.Tests.lineError (line: Text) (parser: () → {Parse Char} a): Text :=
  Parse.Tests.lineResult line parser |> .errorOrElse ""

test "Parse: char" := Parse.Tests.lineError "a" (() => Parse.char 'a') == ""
test "Parse: char, error" := Parse.Tests.lineError "b" (() => Parse.char 'a') == "column 1: expected 'a', got 'b'"
test "Parse: text" :=
  Parse.Tests.lineResult "p=4" (() =>
    Parse.text "p="
    Parse.nat())
    == Ok 4
test "Parse: text, error" := Parse.Tests.lineError "p-4" (() => Parse.text "p=") == "column 1: expected 'p=', got 'p-'"
test "Parse: satisfy" :=
  Parse.Tests.lineResult "e" (() => Parse.satisfy "a vowel" (char => "aeiou".toList.any (== char))) == Ok 'e'
test "Parse: satisfy, error" :=
  Parse.Tests.lineResult "x" (() => Parse.satisfy "a vowel" (char => "aeiou".toList.any (== char)))
    == Err "column 1: expected a vowel, got 'x'"
test "Parse: takeWhile" :=
  Parse.Tests.lineResult "aab" (() =>
    let run := Parse.takeWhile (== 'a')
    Parse.char 'b'
    run)
    == Ok "aa"
test "Parse: takeWhile, none" := Parse.Tests.lineResult "" (() => Parse.takeWhile (== 'a')) == Ok ""
test "Parse: takeWhile1" := Parse.Tests.lineResult "aa" (() => Parse.takeWhile1 "an a" (== 'a')) == Ok "aa"
test "Parse: takeWhile1, error" :=
  Parse.Tests.lineResult "b" (() => Parse.takeWhile1 "an a" (== 'a')) == Err "column 1: expected an a, got 'b'"
test "Parse: nat" := Parse.Tests.lineResult "1203" Parse.nat == Ok 1203
test "Parse: nat, error" := Parse.Tests.lineResult "x" Parse.nat == Err "column 1: expected a number, got 'x'"
test "Parse: nat, then the end" :=
  Parse.Tests.lineResult "12x" Parse.nat == Err "column 3: expected the end of the line, got 'x'"
test "Parse: int" := Parse.Tests.lineResult "-12" Parse.int == Ok (-12)
test "Parse: int, positive" := Parse.Tests.lineResult "12" Parse.int == Ok 12
test "Parse: int, leading plus" := Parse.Tests.lineResult "+12" Parse.int == Ok 12
test "Parse: int, negative" := Parse.Tests.lineResult "-99" Parse.int == Ok (-99)
test "Parse: int, error" :=
  Parse.Tests.lineResult "-" Parse.int == Err "column 2: expected a number, got the end of the line"
test "Parse: int, plus alone" :=
  Parse.Tests.lineResult "+" Parse.int == Err "column 2: expected a number, got the end of the line"
test "Parse: digit" := Parse.Tests.lineResult "7" (() => Parse.digit().toNat) == Ok 7
test "Parse: digit, error" :=
  Parse.Tests.lineResult "x" (() => Parse.digit().toNat) == Err "column 1: expected a digit, got 'x'"
test "Parse: spaces" :=
  Parse.Tests.lineResult " \t 5" (() =>
    Parse.spaces()
    Parse.nat())
    == Ok 5
test "Parse: spaces1" :=
  Parse.Tests.lineResult " 5" (() =>
    Parse.spaces1()
    Parse.nat())
    == Ok 5
test "Parse: spaces1, error" := Parse.Tests.lineError "5" Parse.spaces1 == "column 1: expected a space, got '5'"
test "Parse: token" :=
  Parse.Tests.lineResult " 1 \t2 " (() => (Parse.many1 (() => Parse.token Parse.nat)).toList) == Ok [1, 2]
test "Parse: token, error" :=
  Parse.Tests.lineResult " 1 x" (() => (Parse.many1 (() => Parse.token Parse.nat)).toList)
    == Err "column 4: expected a number or the end of the line, got 'x'"
--| `|>` runs the value's parsers first, then `before` reads the suffix.
test "Parse: before" :=
  Parse.Tests.lineResult "(12,3)" (() =>
    (Parse.char '('; (Parse.nat(), (Parse.char ','; Parse.nat()))) |> Parse.before ")")
    == Ok (12, 3)
test "Parse: before, error" :=
  Parse.Tests.lineResult "12]" (() => Parse.nat() |> Parse.before ")") == Err "column 3: expected ')', got ']'"
test "Parse: newline" :=
  Parse.Tests.lineResult "1\n2" (() => (Parse.sepBy1 Parse.nat Parse.newline).toList) == Ok [1, 2]
test "Parse: newline, CRLF" :=
  Parse.Tests.lineResult "1\r\n2" (() => (Parse.sepBy1 Parse.nat Parse.newline).toList) == Ok [1, 2]
test "Parse: newline, error" := Parse.Tests.lineError "x" Parse.newline == "column 1: expected a line break, got 'x'"
test "Parse: blankLine" := Parse.Tests.lineError "\n\n" Parse.blankLine == ""
test "Parse: blankLine, error" :=
  Parse.Tests.lineError "x" Parse.blankLine == "column 1: expected a blank line, got 'x'"
test "Parse: blankLine, spaces" := Parse.Tests.lineError "\n \t\n" Parse.blankLine == ""
--| A blank line that fails part way is reported where it got to.
test "Parse: blankLine, a line that is not blank" :=
  Parse.Tests.lineError "\n x\n" Parse.blankLine == "line 2, column 2: expected a blank line, got 'x'"
test "Parse: lineEnd" :=
  Parse.Tests.lineResult "1\n2" (() => (Parse.sepBy1 (() => Parse.nat()) Parse.lineEnd).toList) == Ok [1, 2]
test "Parse: lineEnd, error" :=
  Parse.Tests.lineError "x" Parse.lineEnd == "column 1: expected the end of the line, got 'x'"
test "Parse: end" := Parse.Tests.lineError "" Parse.end == ""
test "Parse: pick" := Parse.Tests.lineResult "R" (() => Parse.pick [("L", 1), ("R", 2)]) == Ok 2
test "Parse: pick, error" :=
  Parse.Tests.lineResult "X" (() => Parse.pick [("L", 1), ("R", 2)]) == Err "column 1: expected 'L' or 'R', got 'X'"
--| What was found is shown as long as the longest word expected.
test "Parse: pick, error, longer words" :=
  Parse.Tests.lineResult "mul ( 1,2)" (() => Parse.pick [("mul(", 1), ("do()", 2), ("don't()", 3)])
    == Err "column 1: expected 'mul(', 'do()' or 'don't()', got 'mul ( 1'"
--| Three or more expectations are an English list.
test "Parse: pick, error, three words" :=
  Parse.Tests.lineResult "X" (() => Parse.pick [("L", 1), ("R", 2), ("S", 3)])
    == Err "column 1: expected 'L', 'R' or 'S', got 'X'"
--| The word a short look stops inside is shown whole.
test "Parse: found, to the end of the word" :=
  Parse.Tests.lineError "ab OR cd" (() => Parse.text "ab: ") == "column 1: expected 'ab: ', got 'ab OR'"
test "Parse: pick, first word first" := Parse.Tests.lineResult "<=" (() => Parse.pick [("<=", 0), ("<", 1)]) == Ok 0

test "Parse: optional" :=
  Parse.Tests.lineResult "+5" (() =>
    let sign := Parse.optional (() => Parse.char '+')
    (sign.isSome, Parse.nat()))
    == Ok (True, 5)
test "Parse: optional, absent" :=
  Parse.Tests.lineResult "5" (() =>
    let sign := Parse.optional (() => Parse.char '+')
    (sign.isSome, Parse.nat()))
    == Ok (False, 5)
--| A failed alternative leaves the input as it was, even after reading.
test "Parse: optional backs up" :=
  Parse.Tests.lineResult "abd" (() =>
    let partial := Parse.optional (() =>
      Parse.char 'a'
      Parse.char 'b'
      Parse.char 'c')
    Parse.text "abd"
    partial.isSome)
    == Ok False
test "Parse: oneOf" :=
  Parse.Tests.lineResult "ac" (() =>
    Parse.oneOf [
      () =>
        Parse.text "ab"
        1,
      () =>
        Parse.text "ac"
        2
    ])
    == Ok 2
--| The error is from the furthest point, with everything expected there.
test "Parse: oneOf, error" :=
  Parse.Tests.lineError "ad" (() =>
    Parse.oneOf [
      () =>
        Parse.char 'a'
        Parse.char 'b',
      () =>
        Parse.char 'a'
        Parse.char 'c'
    ])
    == "column 2: expected 'b' or 'c', got 'd'"
test "Parse: many" :=
  Parse.Tests.lineResult "aaab" (() =>
    let found := Parse.many (() => Parse.satisfy "an a" (== 'a'))
    Parse.char 'b'
    found)
    == Ok ['a', 'a', 'a']
test "Parse: many, none" := Parse.Tests.lineResult "" (() => Parse.many Parse.nat) == Ok []
test "Parse: many, reading nothing" :=
  Parse.Tests.lineError "ab" (() => Parse.many Parse.spaces)
    == "column 1: `many`: the parser matched without reading anything"
--| No choice backs out of that failure.
test "Parse: many, reading nothing, inside optional" :=
  Parse.Tests.lineError "ab" (() => Parse.optional (() => Parse.many Parse.spaces))
    == "column 1: `many`: the parser matched without reading anything"
test "Parse: many1" :=
  Parse.Tests.lineResult "aa" (() => (Parse.many1 (() => Parse.satisfy "an a" (== 'a'))).toList) == Ok ['a', 'a']
test "Parse: many1, error" :=
  Parse.Tests.lineResult "" (() => (Parse.many1 (() => Parse.satisfy "an a" (== 'a'))).toList)
    == Err "column 1: expected an a, got the end of the line"
def Parse.Tests.minus(): {Parse Char} (Nat → Nat → Nat) :=
  Parse.char '-'
  (left right => left - right)

test "Parse: chainLeft" := Parse.Tests.lineResult "8-3-2" (() => Parse.chainLeft Parse.nat Parse.Tests.minus) == Ok 3
test "Parse: chainLeft, one operand" :=
  Parse.Tests.lineResult "7" (() => Parse.chainLeft Parse.nat Parse.Tests.minus) == Ok 7
test "Parse: chainLeft, error" :=
  Parse.Tests.lineResult "" (() => Parse.chainLeft Parse.nat Parse.Tests.minus)
    == Err "column 1: expected a number, got the end of the line"
def Parse.Tests.sumOperator (char: Char): Option (Nat → Nat → Nat) :=
  if char == '+' then Some (left right => left + right)
  else if char == '-' then Some (left right => left - right)
  else None

def Parse.Tests.productOperator (char: Char): Option (Nat → Nat → Nat) :=
  if char == '*' then Some (left right => left * right) else None

def Parse.Tests.powerOperator (char: Char): Option (Nat → Nat → Nat) :=
  if char == '^' then Some (left right => Nat.pow left right) else None

--| `+ -` then `*`, each level its own `chainLeft`.
def Parse.Tests.chainTower(): {Parse Char} Nat :=
  Parse.chainLeft (() => Parse.chainLeft Parse.nat (() => Parse.one "an operator" Parse.Tests.productOperator)) (() =>
    Parse.one "an operator" Parse.Tests.sumOperator)

def Parse.Tests.operatorLevels: List (Parse.Level Char Nat) := [
  { associativity = LeftAssociative, operator = Parse.Tests.sumOperator },
  { associativity = LeftAssociative, operator = Parse.Tests.productOperator }
]

--| The same grammar by `Parse.operators`.
def Parse.Tests.climbing(): {Parse Char} Nat := Parse.operators "an operator" Parse.Tests.operatorLevels Parse.nat

--| Samples from clean to broken: a dangling operator, a tighter operator
--| after a looser one, a doubled operator, a space, nothing.
def Parse.Tests.operatorSamples: List Text := ["7", "8-3-2", "1+2*3", "2*3+4", "2*3*4-1+1", "1+", "1+2*", "1*+2",
  "1++2", "1 +2", "", "+1", "2*3-", "4-1*2*", "1+2x"]

test "Parse.operators: same results and messages as a chainLeft tower" := Parse.Tests.operatorSamples.all (sample =>
  Parse.Tests.lineResult sample Parse.Tests.chainTower == Parse.Tests.lineResult sample Parse.Tests.climbing)

test "Parse.operators: precedence" := Parse.Tests.lineResult "1+2*3+4" Parse.Tests.climbing == Ok 11
test "Parse.operators: from the left" := Parse.Tests.lineResult "9-3-2" Parse.Tests.climbing == Ok 4
test "Parse.operators: dangling operator is left unread" :=
  Parse.Tests.lineResult "1+" Parse.Tests.climbing == Err "column 3: expected a number, got the end of the line"
test "Parse.operators: unread operator expected where none follows" :=
  Parse.Tests.lineResult "1x" Parse.Tests.climbing
    == Err "column 2: expected an operator or the end of the line, got 'x'"

def Parse.Tests.powerLevels: List (Parse.Level Char Nat) := [
  { associativity = LeftAssociative, operator = Parse.Tests.sumOperator },
  { associativity = RightAssociative, operator = Parse.Tests.powerOperator }
]

--| `2^3^2` is `2^(3^2)` = 512, where from the left it would be 64.
test "Parse.operators: right associative" :=
  Parse.Tests.lineResult "2^3^2" (() => Parse.operators "an operator" Parse.Tests.powerLevels Parse.nat) == Ok 512

test "Parse.operators: right associative level binds tighter than the one before" :=
  Parse.Tests.lineResult "1+2^3^2-1" (() => Parse.operators "an operator" Parse.Tests.powerLevels Parse.nat) == Ok 512

--| A number and the spaces after it.
def Parse.Tests.spacedNumber(): {Parse Char} Nat :=
  let number := Parse.nat()
  Parse.spaces()
  number

test "Parse.manyToEnd: to the end of the input" :=
  Parse.Tests.lineResult "12 3 45" (() => Parse.manyToEnd "a number" (start => Parse.Tests.spacedNumber()))
    == Ok [12, 3, 45]
test "Parse.manyToEnd: no input" :=
  Parse.Tests.lineResult "" (() => Parse.manyToEnd "a number" (start => Parse.Tests.spacedNumber())) == Ok []
test "Parse.manyToEnd: the parser is given where it starts" :=
  Parse.Tests.lineResult "12 3" (() => Parse.manyToEnd "a number" (start => (start.offset, Parse.Tests.spacedNumber())))
    == Ok [(0, 12), (3, 3)]
--| What is noted at the end is `many`'s, so a parser that goes on there reads the same message.
test "Parse.manyToEnd: the same message as many at the end" :=
  Parse.Tests.lineResult "1 2" (() =>
    let found := Parse.manyToEnd "a number" (start => Parse.Tests.spacedNumber())
    Parse.char 'x'
    found)
    == Parse.Tests.lineResult "1 2" (() =>
      let found := Parse.many Parse.Tests.spacedNumber
      Parse.char 'x'
      found)
test "Parse.manyToEnd: a failing round fails the parse" :=
  Parse.Tests.lineResult "12 x" (() => Parse.manyToEnd "a number" (start => Parse.Tests.spacedNumber()))
    == Err "column 4: expected a number, got 'x'"
test "Parse.manyToEnd: a round that reads nothing" :=
  Parse.Tests.lineError "ab" (() => Parse.manyToEnd "a thing" (start => ()))
    == "column 1: `manyToEnd`: the parser matched without reading anything"
--| Nested lists of numbers, each number times its depth, the outer list's
--| items being at depth 2: "[1,[2,[]],3]" is 1 * 2 + 2 * 3 + 3 * 2 = 14.
def Parse.Tests.depthSum(): {Parse Char} Nat :=
  Parse.recursiveWith
    (nested depth =>
      Parse.oneOf [
        () => depth * Parse.nat(),
        () =>
          Parse.char '['
          let items := Parse.sepBy (() => nested (depth + 1)) (() => Parse.char ',')
          Parse.char ']'
          items.sum
      ])
    1

test "Parse.loop: until the step says stop" :=
  Parse.Tests.lineResult "123x" (() =>
    let digits := Parse.loop (() => Parse.next Parse.isDigit)
    let rest := Parse.span (char => True)
    (digits, rest))
    == Ok (['1', '2', '3'], ['x'])

test "Parse.loop: the step is called at the end, which stops it" :=
  Parse.Tests.lineResult "12" (() => Parse.loop (() => Parse.next Parse.isDigit)) == Ok ['1', '2']

test "Parse.loop: no input" := Parse.Tests.lineResult "" (() => Parse.loop (() => Parse.next Parse.isDigit)) == Ok []

test "Parse.loop: a failing round fails the parse" :=
  Parse.Tests.lineResult "12x" (() => Parse.loop (() => Some (Parse.nat())))
    == Err "column 3: expected a number, got 'x'"

test "Parse.loop: a round that goes on without reading stops the parse" :=
  Parse.Tests.lineError "ab" (() => Parse.loop (() => Some ()))
    == "column 1: `loop`: the step went on without reading anything"

test "Parse.loop: a long input needs no more fuel than the items left" :=
  Parse.whole (List.replicate 300 '7') (() => Parse.loop (() => Parse.next Parse.isDigit))
    == Ok (List.replicate 300 '7')

test "Parse.recursiveWith: the argument changes with the nesting" :=
  Parse.Tests.lineResult "[1,[2,[]],3]" Parse.Tests.depthSum == Ok 14
test "Parse.recursiveWith: a bad nested part" :=
  Parse.Tests.lineResult "[1,[x]]" Parse.Tests.depthSum == Err "column 5: expected a number, '[' or ']', got 'x'"
test "Parse.recursiveWith: left recursion stops the parse" :=
  Parse.Tests.lineError "ab" (() => (Parse.recursiveWith (self depth => self depth) 0: Nat))
    == "column 1: `recursiveWith`: the parser called itself without reading anything"
test "Parse.lastRead: the last character read since a mark" :=
  Parse.Tests.lineResult "abc" (() =>
    let start := Parse.mark()
    Parse.text "ab"
    let last := Parse.lastRead start Parse.mark()
    Parse.char 'c'
    last)
    == Ok (Some 'b')
test "Parse.lastRead: nothing read" :=
  Parse.Tests.lineResult "abc" (() =>
    let start := Parse.mark()
    let last := Parse.lastRead start Parse.mark()
    Parse.text "abc"
    last)
    == Ok None
test "Parse.lastRead: after a span, from a later mark" :=
  Parse.Tests.lineResult "abcd" (() =>
    Parse.char 'a'
    let start := Parse.mark()
    let run := Parse.span (char => char != 'd')
    let last := Parse.lastRead start Parse.mark()
    Parse.char 'd'
    last)
    == Ok (Some 'c')
test "Parse: sepBy" :=
  Parse.Tests.lineResult "1,2,3" (() => Parse.sepBy Parse.nat (() => Parse.char ',')) == Ok [1, 2, 3]
test "Parse: sepBy, none" := Parse.Tests.lineResult "" (() => Parse.sepBy Parse.nat (() => Parse.char ',')) == Ok []
test "Parse: sepBy1, error" :=
  Parse.Tests.lineResult "1,2," (() => (Parse.sepBy1 Parse.nat (() => Parse.char ',')).toList)
    == Err "column 5: expected a number, got the end of the line"
test "Parse: lines" := Parse.Tests.allResult "1\n2\n" (() => (Parse.lines Parse.nat).toList) == Ok [1, 2]
test "Parse: lines, error" :=
  Parse.Tests.allResult "1\n2\nx\n" (() => (Parse.lines Parse.nat).toList)
    == Err "line 3, column 1: expected a number or the end of the input, got 'x'"
test "Parse: sections" :=
  Parse.Tests.allResult "1\n2\n\n3\n" (() => (Parse.sections (() => (Parse.lines Parse.nat).toList)).toList)
    == Ok [[1, 2], [3]]
--| A missing blank line is expected where the next section starts, with the
--| end of the input.
test "Parse: sections, no blank line" :=
  Parse.Tests.allResult "1,2\n3,4\n" (() =>
    (Parse.sections (() => (Parse.sepBy1 Parse.nat (() => Parse.char ',')).toList)).toList)
    == Err "line 2, column 1: expected a blank line or the end of the input, got '3'"
--| A second blank line is where the next section should start, not the end of
--| the input after the line breaks.
test "Parse: sections, two blank lines" :=
  Parse.Tests.allResult "a\n\n\nb" (() =>
    (Parse.sections (() => (Parse.lines (() => Parse.pick [("a", 1), ("b", 2)])).toList)).toList)
    == Err "line 3, column 1: expected 'a' or 'b', got the end of the line"
--| Blank lines before more input that nothing else reads: the blank line is
--| what is wrong.
test "Parse: all, blank line before extra input" :=
  Parse.Tests.allResult "1\n\nfoo" (() => Parse.nat ())
    == Err "line 2, column 1: expected the end of the input, got a blank line"
test "Parse: all, one line break before extra input" :=
  Parse.Tests.allResult "1\nfoo" (() => Parse.nat ()) == Err "line 2, column 1: expected the end of the input, got 'f'"
test "Parse: grid" :=
  Parse.Tests.allResult "@.\n.@\n" (() =>
    (Parse.grid (() => Parse.pick [("@", True), (".", False)])).toList |> .map (row => row.toList))
    == Ok [[True, False], [False, True]]
test "Parse: grid, error" :=
  Parse.Tests.allResult "@.\n.x\n" (() =>
    (Parse.grid (() => Parse.pick [("@", True), (".", False)])).toList |> .map (row => row.toList))
    == Err "line 2, column 2: expected '@', '.' or the end of the line, got 'x'"
test "Parse: looseGrid" :=
  Parse.Tests.allResult "@.\n\n.\n" (() => Parse.looseGrid (() => Parse.pick [("@", True), (".", False)]))
    == Ok [[True, False], [], [False]]
test "Parse: looseGrid, no rows" :=
  Parse.Tests.allResult "" (() => Parse.looseGrid (() => Parse.pick [("@", True), (".", False)])) == Ok []
test "Parse: looseGrid, error" :=
  Parse.Tests.allResult "@.\n.x\n" (() => Parse.looseGrid (() => Parse.pick [("@", True), (".", False)]))
    == Err "line 2, column 2: expected '@', '.' or the end of the line, got 'x'"
test "Parse: label" :=
  Parse.Tests.lineResult "X5" (() => Parse.label "a turn like L68" (() => Parse.pick [("L", 1), ("R", 2)]))
    == Err "column 1: expected a turn like L68, got 'X'"
--| A labelled parser that got further reports what it expected there.
test "Parse: label, further in" :=
  Parse.Tests.lineResult "1,x" (() =>
    Parse.label "a pair like 1,2" (() =>
      let left := Parse.nat()
      Parse.char ','
      (left, Parse.nat())))
    == Err "column 3: expected a number, got 'x'"

--| Nested lists of numbers, summed: "[1,[2,[]],3]".
def Parse.Tests.nestedSum(): {Parse Char} Nat := Parse.recursive (nested =>
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
test "Parse: recursive, left recursion" :=
  Parse.Tests.lineResult "1+2" (() =>
    Parse.recursive (self =>
      let left := self()
      Parse.char '+'
      left + Parse.nat()))
    == Err "column 1: `recursive`: the parser called itself without reading anything"

test "Parse: fail" := Parse.Tests.lineResult "a" (() => (Parse.fail "no": Nat)) == Err "column 1: no"
test "Parse: expected" :=
  Parse.Tests.lineResult "a" (() => (Parse.expected "a b": Nat)) == Err "column 1: expected a b, got 'a'"
--| A message and an expectation at the same point are both reported.
test "Parse: fail beside expected" :=
  Parse.Tests.lineError "y" (() => Parse.oneOf [() => Parse.fail "not this", () => Parse.char 'x'])
    == "column 1: not this; expected 'x', got 'y'"
test "Parse: ensure" :=
  Parse.Tests.lineResult "5" (() =>
    let number := Parse.nat()
    Parse.ensure (number > 9) "too small"
    number)
    == Err "column 2: too small"
--| What `many1` tried after the last digit is dropped for the message.
test "Parse: ensure after a repetition" :=
  Parse.Tests.lineResult "12" (() =>
    let digits := Parse.many1 Parse.digit |> .toList
    Parse.ensure (digits.length > 2) "too few digits"
    digits.length)
    == Err "column 3: too few digits"
--| A tab and the end of the input are named, not shown.
test "Parse: got a tab" := Parse.Tests.lineError "\t" (() => Parse.char 'a') == "column 1: expected 'a', got a tab"
test "Parse: got the end of the input" :=
  Parse.Tests.allResult "1," (() => (Parse.sepBy1 Parse.nat (() => Parse.char ',')).toList)
    == Err "line 1, column 3: expected a number, got the end of the input"
test "Parse: need" :=
  Parse.Tests.lineResult "" (() => Parse.need (None: Option Nat) "nothing") == Err "column 1: nothing"
test "Parse: fromFail" :=
  Parse.Tests.lineResult "ab" (() =>
    let word := Parse.takeWhile (char => char ≠ ' ')
    Parse.fromFail (() => word.toNatOrFail))
    == Err "column 3: expected a whole number, got 'ab'"
test "Parse: fromFail, success" :=
  Parse.Tests.lineResult "12" (() =>
    let word := Parse.takeWhile (char => char ≠ ' ')
    Parse.fromFail (() => word.toNatOrFail))
    == Ok 12

test "Parse: all" :=
  Parse.Tests.allResult "1,2\n3,4" (() =>
    (Parse.lines (() => (Parse.sepBy1 Parse.nat (() => Parse.char ',')).toList)).toList)
    == Ok [[1, 2], [3, 4]]
test "Parse: all, error" :=
  Parse.Tests.allResult "1,2\n3;4\n" (() =>
    (Parse.lines (() => (Parse.sepBy1 Parse.nat (() => Parse.char ',')).toList)).toList)
    == Err "line 2, column 2: expected ',' or the end of the line, got ';'"
test "Parse: all, one line" :=
  Parse.Tests.allResult "1,2x" (() => (Parse.sepBy1 Parse.nat (() => Parse.char ',')).toList)
    == Err "line 1, column 4: expected ',' or the end of the line, got 'x'"
test "Parse: eachLine" :=
  Fail.toResult (() => Parse.eachLine "1,2\n3,4\n" (() => (Parse.sepBy1 Parse.nat (() => Parse.char ',')).toList))
    == Ok [[1, 2], [3, 4]]
test "Parse: eachLine, error" :=
  Fail.toResult (() => Parse.eachLine "1,2\n3x4" (() => (Parse.sepBy1 Parse.nat (() => Parse.char ',')).toList))
    == Err "line 2, column 2: expected ',' or the end of the line, got 'x'"
test "Parse: eachLine, empty" := Fail.toResult (() => Parse.eachLine "" Parse.nat) == Ok []
--| A failure keeps its line under `Fail.context`.
test "Parse: eachLine, in context" :=
  Fail.toResult (() => Fail.context "input" (() => Parse.eachLine "x" Parse.nat))
    == Err "input: line 1, column 1: expected a number, got 'x'"
test "Parse: all, trailing blank lines" :=
  Parse.Tests.allResult "1\n2\n\n\n" (() => (Parse.lines Parse.nat).toList) == Ok [1, 2]
test "Parse: line, a final line break" := Parse.Tests.lineResult "12\n" Parse.nat == Ok 12
test "Parse: line, two final line breaks" :=
  Parse.Tests.lineResult "12\n\n" Parse.nat == Err "line 2, column 1: expected the end of the input, got a line break"
test "Parse: line, a second line" :=
  Parse.Tests.lineResult "12\n34\n" Parse.nat == Err "line 2, column 1: expected the end of the input, got '3'"
test "Parse: line, an error on a second line" :=
  Parse.Tests.lineResult "1\n2x" (() => (Parse.sepBy1 Parse.nat Parse.newline).toList)
    == Err "line 2, column 2: expected the end of the line, got 'x'"

test "Parse: ensureAt" :=
  Parse.Tests.lineResult "x=12345" (() =>
    Parse.text "x="
    let start := Parse.mark()
    let number := Parse.nat()
    let finish := Parse.mark()
    Parse.ensureAt start (finish.offset - start.offset ≤ 3) "too long"
    number)
    == Err "column 3: too long"
test "Parse: natDigits" := Parse.Tests.lineResult "123" (() => Parse.natDigits 1 3) == Ok 123
test "Parse: natDigits, too long" :=
  Parse.Tests.lineResult "x1234" (() =>
    Parse.char 'x'
    Parse.natDigits 1 3)
    == Err "column 2: expected a number of 1 to 3 digits, got '1'"
test "Parse: natDigits, too short" :=
  Parse.Tests.lineResult "12" (() => Parse.natDigits 3 3) == Err "column 1: expected a 3-digit number, got '1'"
test "Parse: natDigits, none" :=
  Parse.Tests.lineResult "x" (() => Parse.natDigits 0 3) == Err "column 1: expected a number of 1 to 3 digits, got 'x'"
test "Parse: natDigits, a range" :=
  Parse.Tests.lineResult "123456" (() => Parse.natDigits 2 5)
    == Err "column 1: expected a number of 2 to 5 digits, got '1'"
test "Parse: natDigits, one digit" :=
  Parse.Tests.lineResult "10" (() => Parse.natDigits 1 1) == Err "column 1: expected a 1-digit number, got '1'"
test "Parse: repeat" :=
  Parse.Tests.lineResult "aab" (() =>
    let found := Parse.repeat (atLeast := 1) (atMost := 3) (() => Parse.satisfy "an a" (== 'a'))
    Parse.char 'b'
    found)
    == Ok ['a', 'a']
test "Parse: repeat, at most" :=
  Parse.Tests.lineResult "aaaa" (() =>
    let found := Parse.repeat (atLeast := 1) (atMost := 3) (() => Parse.satisfy "an a" (== 'a'))
    Parse.char 'a'
    found)
    == Ok ['a', 'a', 'a']
test "Parse: repeat, too few" :=
  Parse.Tests.lineResult "ab" (() => Parse.repeat (atLeast := 2) (atMost := 3) (() => Parse.satisfy "an a" (== 'a')))
    == Err "column 2: expected an a, got 'b'"
test "Parse: exactly" :=
  Parse.Tests.lineResult "123" (() => Parse.exactly 3 Parse.digit |> .map (digit => digit.toNat)) == Ok [1, 2, 3]
test "Parse: exactly, too few" :=
  Parse.Tests.lineResult "12" (() => Parse.exactly 3 Parse.digit)
    == Err "column 3: expected a digit, got the end of the line"

--| The values of `nat` among other characters.
def Parse.Tests.numbers (line: Text): Result (List Nat) Text :=
  Parse.Tests.lineResult line (() => Parse.findAll Parse.nat)

test "Parse: findAll" := Parse.Tests.numbers "a1b22c333" == Ok [1, 22, 333]
test "Parse: findAll, none" := Parse.Tests.numbers "abc" == Ok []
test "Parse: findAll, empty input" := Parse.Tests.numbers "" == Ok []
--| A failed try reads nothing, so a match can start inside it.
test "Parse: findAll, inside a failed try" :=
  Parse.Tests.lineResult "aab" (() => Parse.findAll (() => Parse.text "ab")) == Ok [()]
test "Parse: findAll, a match that reads nothing" :=
  Parse.Tests.lineResult "ab" (() => Parse.findAll (() => Parse.mark().offset)) == Ok [0, 1, 2]
test "Parse: findAllStarting" :=
  Parse.Tests.lineResult "a1b22c333" (() => Parse.findAllStarting Parse.isDigit Parse.nat) == Ok [1, 22, 333]

--| Two sections of different things: rules like "1|2", a blank line, then
--| lists like "1,2".
def Parse.Tests.twoSections (input: Text): Result (List (Nat, Nat), List (List Nat)) Text :=
  Parse.Tests.allResult input (() =>
    let rules := Parse.section (() =>
      let before := Parse.nat()
      Parse.char '|'
      (before, Parse.nat()))
    let lists := Parse.lines (() => (Parse.sepBy1 Parse.nat (() => Parse.char ',')).toList)
    (rules.toList, lists.toList))

test "Parse: section" := Parse.Tests.twoSections "1|2\n3|4\n\n1,2\n3\n" == Ok ([(1, 2), (3, 4)], [[1, 2], [3]])
test "Parse: section, trailing blank lines" := Parse.Tests.twoSections "1|2\n\n1,2\n\n\n" == Ok ([(1, 2)], [[1, 2]])
test "Parse: section, no blank line" :=
  Parse.Tests.twoSections "1|2\n1,2\n" == Err "line 2, column 2: expected '|' or a blank line before this line, got ','"
test "Parse: section, a bad line" :=
  Parse.Tests.twoSections "1|2\n3x4\n\n1,2\n"
    == Err "line 2, column 2: expected '|' or a blank line before this line, got 'x'"
test "Parse: section, a bad first line" :=
  Parse.Tests.twoSections "1x2\n\n1,2\n" == Err "line 1, column 2: expected '|', got 'x'"
test "Parse: section, blank line of spaces" := Parse.Tests.twoSections "1|2\n  \n1,2\n" == Ok ([(1, 2)], [[1, 2]])
test "Parse: section, nothing after" :=
  Parse.Tests.twoSections "1|2\n3|4\n"
    == Err "line 3, column 1: expected a number or a blank line, got the end of the input"
