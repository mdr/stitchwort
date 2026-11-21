import Parse.Problem (Expected, Literal, Literals)
import Effect.AlwaysTreeOf (AlwaysCall)

-- `Parse.Runs` lemmas for the character pieces of Parse/Chars.sw and the
-- text runners, with the examples; the generic ones are in Parse/Runs.sw.

--| `char expected` where the input starts with it.
theorem Parse.runsChar ∀ (expected: Char) (rest: List Char):
    Parse.Runs (() => Parse.char expected) [expected] rest () :=
  Parse.runsMap
    (() => Parse.satisfy "'${expected}'" (== expected))
    (x => ())
    [expected]
    rest
    expected
    (Parse.runsSatisfy "'${expected}'" (== expected) expected rest (Parse.sameChar expected))

--| `text expected` where the input starts with it.
theorem Parse.runsText ∀ (expected: Text) (rest: List Char):
    Parse.Runs (() => Parse.text expected) expected.toList rest () :=
  state starts honest =>
    let lengths: state.at.rest.length = expected.toList.length + rest.length :=
      rewrite starts then List.lengthAppend expected.toList rest
    Witness
      (state.advance rest expected.toList.length).at
      (Both
        (rewrite Parse.runFromTextThere state expected rest _ starts)
        (Both byComputing (Both (arithmetic [honest, lengths]) (arithmetic [List.lengthAppend expected.toList rest]))))

--| `nat` on a run of digits, with `rest` not starting with another digit (the
--| digits are read to the end, so "12" isn't 1 followed by 2): it reads `digits`
--| and gives their value (leading zeros are fine: "007" is 7).
theorem Parse.runsNat ∀ (digits rest: List Char)
    (some: digits ≠ [])
    (all: digits.all Parse.isDigit = True)
    (stops: rest.takeWhile Parse.isDigit = []):
    Parse.Runs Parse.nat digits rest (Parse.digitsValue digits) :=
  state starts honest =>
    let lengths: state.at.rest.length = digits.length + rest.length := rewrite starts then List.lengthAppend digits rest
    Witness
      (state.advance rest digits.length).at
      (Both
        (rewrite Parse.runFromNatThere state digits rest _ starts some all stops)
        (Both byComputing (Both (arithmetic [honest, lengths]) (arithmetic [List.lengthAppend digits rest]))))

--| `spaces` on a run of spaces and tabs, with `rest` not starting with one.
theorem Parse.runsSpaces ∀ (blanks rest: List Char)
    (all: blanks.all Parse.isSpace = True)
    (stops: rest.takeWhile Parse.isSpace = []):
    Parse.Runs Parse.spaces blanks rest () :=
  Parse.runsMap
    (() => Parse.span Parse.isSpace)
    (skipped => ())
    blanks
    rest
    blanks
    (Parse.runsSpan Parse.isSpace blanks rest all stops)

--| `token p`: `before` spaces, then what `p` read, then `after` spaces. The
--| input must not have a space where `p`'s part starts (`startsAtToken`: the
--| leading spaces are all of them) and `rest` doesn't start with one (the
--| trailing ones are).
theorem Parse.runsToken ∀ (p: () → {Parse Char} a) (before inside after rest: List Char) (v: a)
    (spacesBefore: before.all Parse.isSpace = True)
    (startsAtToken: (inside ++ (after ++ rest)).takeWhile Parse.isSpace = [])
    (spacesAfter: after.all Parse.isSpace = True)
    (stopsAfter: rest.takeWhile Parse.isSpace = [])
    (runsInside: Parse.Runs p inside (after ++ rest) v):
    Parse.Runs (() => Parse.token p) (before ++ (inside ++ after)) rest v :=
  Parse.runsBind Parse.spaces
    (u =>
      let value := p()
      Parse.spaces()
      value)
    before
    (inside ++ after)
    (before ++ (inside ++ after))
    rest
    ()
    v
    byComputing
    (rewrite List.appendAssoc inside after rest then
      Parse.runsSpaces before (inside ++ (after ++ rest)) spacesBefore startsAtToken)
    (Parse.runsBind p
      (value =>
        Parse.spaces()
        value)
      inside
      after
      (inside ++ after)
      rest
      v
      v
      byComputing
      runsInside
      (Parse.runsBind Parse.spaces
        (u => v)
        after
        []
        after
        rest
        ()
        v
        (List.appendNil after).flipped
        (Parse.runsSpaces after rest spacesAfter stopsAfter)
        (Parse.runsPure v rest)))

--| `text expected` declines where the input doesn't start with it.
theorem Parse.declinesText ∀ (expected: Text) (input: List Char)
    (absent: Text.stripPrefixChars expected.toList input = None):
    Parse.Declines (() => Parse.text expected) input :=
  state starts honest => rewrite starts, Parse.stripPrefixBySameChar input expected.toList, absent

--| `nat` declines where the input doesn't start with a digit.
theorem Parse.declinesNat ∀ (input: List Char)
    (stops: input.takeWhile Parse.isDigit = []):
    Parse.Declines Parse.nat input :=
  state starts honest => rewrite starts, List.spanAppend Parse.isDigit [] input byComputing stops

--| `char` declines at the end of the input.
theorem Parse.declinesCharEnd ∀ (expected: Char): Parse.Declines (() => Parse.char expected) [] :=
  Parse.declinesBind
    (() => Parse.satisfy "'${expected}'" (== expected))
    (c => ())
    []
    (Parse.declinesSatisfyEnd "'${expected}'" (== expected))

--| `char expected` declines where the next character is another.
theorem Parse.declinesChar ∀ (expected char: Char) (rest: List Char)
    (other: (char == expected) = False):
    Parse.Declines (() => Parse.char expected) [char, ..rest] :=
  Parse.declinesBind
    (() => Parse.satisfy "'${expected}'" (== expected))
    (c => ())
    [char, ..rest]
    (Parse.declinesSatisfy "'${expected}'" (== expected) char rest other)

def Parse.RunsExamples.add (x y: Nat): Nat := x + y

def Parse.RunsExamples.plus(): {Parse Char} (Nat → Nat → Nat) :=
  Parse.char '+'
  Parse.RunsExamples.add

def Parse.RunsExamples.sum(): {Parse Char} Nat := Parse.chainLeft Parse.nat Parse.RunsExamples.plus

--| "1+2" parses as a sum with `chainLeft` to 3, by `Runs` lemmas alone.
theorem Parse.runsSumExample: Parse.run ['1', '+', '2'] Parse.RunsExamples.sum = Ok 3 :=
  Parse.runsRun Parse.RunsExamples.sum
    ['1', '+', '2']
    3
    (Parse.runsChainLeft Parse.nat Parse.RunsExamples.plus
      ['1']
      1
      [(['+', '2'], (Parse.RunsExamples.add, 2))]
      []
      (Parse.runsNat ['1'] ['+', '2'] (List.consNotNil '1' []) byComputing byComputing)
      (Both
        (List.consNotNil '+' ['2'])
        (Both
          (Parse.runsChainStep Parse.nat Parse.RunsExamples.plus
            ['+']
            ['2']
            []
            Parse.RunsExamples.add
            2
            (Parse.runsBind
              (() => Parse.char '+')
              (u => Parse.RunsExamples.add)
              ['+']
              []
              ['+']
              ['2']
              ()
              Parse.RunsExamples.add
              (Eq.flipped (List.appendNil ['+']))
              (Parse.runsChar '+' ['2'])
              (Parse.runsPure Parse.RunsExamples.add ['2']))
            (Parse.runsNat ['2'] [] (List.consNotNil '2' []) byComputing byComputing))
          (Parse.declinesChainStep Parse.nat Parse.RunsExamples.plus []
            (Parse.declinesBind (() => Parse.char '+') (u => Parse.RunsExamples.add) [] (Parse.declinesCharEnd '+'))))))

--| None of `choices`' words is a start of `input`.
def Parse.WordsAbsent (input: List Char): (choices: List (Text, a)) → Prop
  | [] => True = True
  | [choice, ..more] => Text.stripPrefixChars choice.fst.toList input = None ∧ Parse.WordsAbsent input more

--| The search `pick` makes, past the words of `before` that don't start the input,
--| finds `found`, whose word does.
theorem Parse.runsFindWord ∀ (found: (Text, a)) (later: List (Text, a)) (rest: List Char) (before: List (Text, a))
    (absent: Parse.WordsAbsent (found.fst.toList ++ rest) before):
    Parse.Runs
      (() =>
        (before ++ [found, ..later]).find (choice => Parse.literal { items = choice.fst.toList, same = Text.sameChar }))
      found.fst.toList
      rest
      (Some found) :=
  match before, absent with
    | [], absent => state starts honest =>
      Parse.runsBind
        (() => Parse.literal { items = found.fst.toList, same = Text.sameChar })
        (hit =>
          if hit then Some found
          else later.find (choice => Parse.literal { items = choice.fst.toList, same = Text.sameChar }))
        found.fst.toList
        []
        found.fst.toList
        rest
        True
        (Some found)
        (List.appendNil found.fst.toList).flipped
        (Parse.runsLiteral { items = found.fst.toList, same = Text.sameChar } Text.sameCharRefl rest)
        (Parse.runsPure (Some found) rest)
        state
        starts
        honest
    | [choice, ..more], Both gone absent => state starts honest =>
      match Parse.runsFindWord found later rest more absent state starts honest with
        | Witness m (Both ran others) =>
          Witness m
            (Both
              (Eq.trans
                (rewrite starts, Parse.stripPrefixBySameChar (found.fst.toList ++ rest) choice.fst.toList, gone)
                ran)
              others)

--| `pick` where `word` is the first of the choices to come next: `before` are the
--| choices tried first, none of which starts the input (words are tried in
--| order, so a word that starts another must come after it), and `later` the
--| rest. It reads `word` and gives its value.
theorem Parse.runsPick ∀ (before: List (Text, a)) (word: Text) (value: a) (later: List (Text, a)) (rest: List Char)
    (absent: Parse.WordsAbsent (word.toList ++ rest) before):
    Parse.Runs (() => Parse.pick (before ++ [(word, value), ..later])) word.toList rest value :=
  Parse.runsBind
    (() =>
      (before ++ [(word, value), ..later]).find (choice =>
        Parse.literal { items = choice.fst.toList, same = Text.sameChar }))
    (found =>
      match found with
        | Some (word2, value2) => value2
        | None =>
          Parse.noteWords (before ++ [(word, value), ..later])
          Empty.absurd Parse.stop())
    word.toList
    []
    word.toList
    rest
    (Some (word, value))
    value
    (List.appendNil word.toList).flipped
    (Parse.runsFindWord (word, value) later rest before absent)
    (Parse.runsPure value rest)

--| `noteWords` reads nothing.
theorem Parse.runsNoteWords ∀ (rest: List Char) (words: List (Text, a)):
    Parse.Runs (() => Parse.noteWords words) [] rest () :=
  match words with
    | [] => state starts honest => Parse.runsPure () rest state starts honest
    | [choice, ..more] => state starts honest =>
      Parse.runsNote (Literals ([choice, ..more].map (choice => choice.fst))) rest state starts honest

--| The search `pick` makes, when none of the words comes next, finds none.
theorem Parse.runsFindNone ∀ (rest: List Char) (choices: List (Text, a))
    (absent: Parse.WordsAbsent rest choices):
    Parse.Runs
      (() => choices.find (choice => Parse.literal { items = choice.fst.toList, same = Text.sameChar }))
      []
      rest
      None :=
  match choices, absent with
    | [], absent => state starts honest => Parse.runsPure None rest state starts honest
    | [choice, ..more], Both gone absent => state starts honest =>
      match Parse.runsFindNone rest more absent state starts honest with
        | Witness m (Both ran others) =>
          Witness m
            (Both (Eq.trans (rewrite starts, Parse.stripPrefixBySameChar rest choice.fst.toList, gone) ran) others)

--| `pick` declines where none of its words comes next.
theorem Parse.declinesPick ∀ (choices: List (Text, a)) (input: List Char)
    (absent: Parse.WordsAbsent input choices):
    Parse.Declines (() => Parse.pick choices) input :=
  Parse.declinesAfter
    (() => choices.find (choice => Parse.literal { items = choice.fst.toList, same = Text.sameChar }))
    (found =>
      match found with
        | Some (word2, value2) => value2
        | None =>
          Parse.noteWords choices
          Empty.absurd Parse.stop())
    []
    input
    None
    (Parse.runsFindNone input choices absent)
    (Parse.declinesAfter
      (() => Parse.noteWords choices)
      (u => Empty.absurd Parse.stop())
      []
      input
      ()
      (Parse.runsNoteWords input choices)
      (Parse.declinesStop input))

--| `pick` takes the first word that comes next: "*" after "+" fails to start "*x".
theorem Parse.runsPickExample: Parse.Runs (() => Parse.pick [("+", 1), ("*", 2)]) ['*'] ['x'] 2 :=
  Parse.runsPick [("+", 1)] "*" 2 [] ['x'] (Both byComputing byComputing)

--| Each line of `input` runs `p` to its value (`Runs` the line's characters
--| with nothing left over): `Parse.eachLine input p` gives those values. The
--| converse of [`Parse.eachLineReads`].
theorem Parse.runsEachLine ∀ (input: Text) (p: () → {Parse Char} a) (values: List a)
    (runs: List.All2 (line v => Parse.Runs p line [] v) (input.lines.map Text.toList) values):
    Fail.toResult (() => Parse.eachLine input p) = Ok values :=
  rewrite Fail.toResultMap _ input.lines.withIndex then
    Result.traverseOfAll2 _
      (entry v => Parse.Runs p entry.snd.toList [] v)
      (entry v run => match entry with | (index, line) => rewrite Parse.runsWhole line.toList p v run)
      input.lines.withIndex
      values
      (List.all2OfWithIndex
        (line v => Parse.Runs p line.toList [] v)
        0
        input.lines
        values
        (List.all2OfMapLeft Text.toList (line v => Parse.Runs p line [] v) input.lines values runs))

--| `newline` on "\n".
theorem Parse.runsNewlineLf ∀ (rest: List Char): Parse.Runs Parse.newline ['\n'] rest () :=
  Parse.runsBind
    (() => Parse.literal { items = ['\n'], same = Text.sameChar })
    (hit =>
      if hit then ()
      else if Parse.literal { items = ['\r', '\n'], same = Text.sameChar } then ()
      else Parse.expected "a line break")
    ['\n']
    []
    ['\n']
    rest
    True
    ()
    byComputing
    (Parse.runsLiteral { items = ['\n'], same = Text.sameChar } Text.sameCharRefl rest)
    (Parse.runsPure () rest)

--| `newline` on "\r\n".
theorem Parse.runsNewlineCrlf ∀ (rest: List Char): Parse.Runs Parse.newline ['\r', '\n'] rest () :=
  Parse.runsBind
    (() => Parse.literal { items = ['\n'], same = Text.sameChar })
    (hit =>
      if hit then ()
      else if Parse.literal { items = ['\r', '\n'], same = Text.sameChar } then ()
      else Parse.expected "a line break")
    []
    ['\r', '\n']
    ['\r', '\n']
    rest
    False
    ()
    byComputing
    (Parse.runsLiteralAbsent { items = ['\n'], same = Text.sameChar } (['\r', '\n'] ++ rest) byComputing)
    (Parse.runsBind
      (() => Parse.literal { items = ['\r', '\n'], same = Text.sameChar })
      (hit => if hit then () else Parse.expected "a line break")
      ['\r', '\n']
      []
      ['\r', '\n']
      rest
      True
      ()
      byComputing
      (Parse.runsLiteral { items = ['\r', '\n'], same = Text.sameChar } Text.sameCharRefl rest)
      (Parse.runsPure () rest))

--| `takeWhile1` declines where nothing passes `passes`.
theorem Parse.declinesTakeWhile1 ∀ (what: Text) (passes: Char → Bool) (input: List Char)
    (stops: input.takeWhile passes = []):
    Parse.Declines (() => Parse.takeWhile1 what passes) input :=
  Parse.declinesAfter
    (() => Parse.span passes) _
    []
    input
    []
    (Parse.runsSpan passes [] input byComputing stops)
    (Parse.declinesExpected what input)

--| `newline` declines where the input starts with neither "\n" nor "\r\n".
theorem Parse.declinesNewline ∀ (input: List Char)
    (noLf: Text.stripPrefixChars ['\n'] input = None)
    (noCrlf: Text.stripPrefixChars ['\r', '\n'] input = None):
    Parse.Declines Parse.newline input :=
  Parse.declinesAfter
    (() => Parse.literal { items = ['\n'], same = Text.sameChar })
    (hit =>
      if hit then ()
      else if Parse.literal { items = ['\r', '\n'], same = Text.sameChar } then ()
      else Parse.expected "a line break")
    []
    input
    False
    (Parse.runsLiteralAbsent
      { items = ['\n'], same = Text.sameChar }
      input
      (Eq.trans (Parse.stripPrefixBySameChar input ['\n']) noLf))
    (Parse.declinesAfter
      (() => Parse.literal { items = ['\r', '\n'], same = Text.sameChar })
      (hit => if hit then () else Parse.expected "a line break")
      []
      input
      False
      (Parse.runsLiteralAbsent
        { items = ['\r', '\n'], same = Text.sameChar }
        input
        (Eq.trans (Parse.stripPrefixBySameChar input ['\r', '\n']) noCrlf))
      (Parse.declinesExpected "a line break" input))

--| `takeWhile1 what passes` on a non-empty run of characters that pass, with
--| `rest` not starting with another: it reads the run and gives it as text.
theorem Parse.runsTakeWhile1 ∀ (what: Text) (passes: Char → Bool) (taken rest: List Char)
    (some: taken ≠ [])
    (all: taken.all passes = True)
    (stops: rest.takeWhile passes = []):
    Parse.Runs (() => Parse.takeWhile1 what passes) taken rest (Text.fromList taken) :=
  match taken with
    | [] => (some byComputing).impossible
    | [char, ..others] =>
      Parse.runsBind
        (() => Parse.span passes)
        (chars =>
          match chars with
            | [] => Parse.expected what
            | others2 => Text.fromList others2)
        [char, ..others]
        []
        [char, ..others]
        rest
        [char, ..others]
        (Text.fromList [char, ..others])
        (Eq.flipped (List.appendNil [char, ..others]))
        (Parse.runsSpan passes [char, ..others] rest all stops)
        (Parse.runsPure (Text.fromList [char, ..others]) rest)

--| `spaces1` on a non-empty run of spaces and tabs, with `rest` not starting
--| with one.
theorem Parse.runsSpaces1 ∀ (blanks rest: List Char)
    (some: blanks ≠ [])
    (all: blanks.all Parse.isSpace = True)
    (stops: rest.takeWhile Parse.isSpace = []):
    Parse.Runs Parse.spaces1 blanks rest () :=
  Parse.runsMap
    (() => Parse.takeWhile1 "a space" Parse.isSpace)
    (skipped => ())
    blanks
    rest
    (Text.fromList blanks)
    (Parse.runsTakeWhile1 "a space" Parse.isSpace blanks rest some all stops)

--| `digit` on a digit character `char` whose value is `d`.
theorem Parse.runsDigit ∀ (char: Char) (d: Fin 10) (rest: List Char)
    (isDigit: Parse.isDigit char = True)
    (value: char.toDigit = Some d):
    Parse.Runs Parse.digit [char] rest d :=
  Parse.runsBind
    (() => Parse.satisfy "a digit" Parse.isDigit)
    (char2 => Parse.need char2.toDigit "expected a digit")
    [char]
    []
    [char]
    rest
    char
    d
    (Eq.flipped (List.appendNil [char]))
    (Parse.runsSatisfy "a digit" Parse.isDigit char rest isDigit)
    (rewrite value then Parse.runsPure d rest)

--| `natDigits atLeast atMost` on a run of `digits` of the right length, with
--| `rest` not starting with another digit (all the digits are read before the
--| count is checked, so "1234" isn't a 3-digit number followed by a 4): it
--| reads them and gives their value.
theorem Parse.runsNatDigits ∀ (atLeast atMost: Nat) (digits rest: List Char)
    (some: digits ≠ [])
    (all: digits.all Parse.isDigit = True)
    (stops: rest.takeWhile Parse.isDigit = [])
    (enough: atLeast ≤ digits.length)
    (notTooMany: digits.length ≤ atMost):
    Parse.Runs (() => Parse.natDigits atLeast atMost) digits rest (Parse.digitsValue digits) :=
  state starts honest =>
    let positive: 0 < digits.length := match digits with
      | [] => (some byComputing).impossible
      | [char, ..others] => arithmetic
    let holds: (0 < digits.length ∧ atLeast ≤ digits.length ≤ atMost) = True :=
      arithmetic [positive, enough, notTooMany]
    Parse.runsFromMark state
      (start =>
        let digits2 := Parse.span Parse.isDigit
        let count := digits2.length
        if 0 < count ∧ atLeast ≤ count ≤ atMost then
          digits2.map (digit => digit.digitValue.getOrElse 0) |> Nat.fromDigits
        else
          Parse.reset start
          let fewest := if atLeast == 0 then 1 else atLeast
          Parse.expected
            (if fewest == atMost then "a ${atMost}-digit number" else "a number of ${fewest} to ${atMost} digits"))
      digits
      rest
      (Parse.digitsValue digits)
      (Parse.runsFromBind state
        (() => Parse.span Parse.isDigit)
        (digits2 =>
          let count := digits2.length
          if 0 < count ∧ atLeast ≤ count ≤ atMost then
            digits2.map (digit => digit.digitValue.getOrElse 0) |> Nat.fromDigits
          else
            Parse.reset state.at
            let fewest := if atLeast == 0 then 1 else atLeast
            Parse.expected
              (if fewest == atMost then "a ${atMost}-digit number" else "a number of ${fewest} to ${atMost} digits"))
        digits
        []
        digits
        rest
        digits
        (Parse.digitsValue digits)
        (List.appendNil digits).flipped
        (Parse.runsSpan Parse.isDigit digits rest all stops)
        (middle atRest honest2 offset => rewrite holds then Parse.runsPure (Parse.digitsValue digits) rest middle))
      starts
      honest

--| A sign character that is not a digit isn't the start of a digit.
theorem Parse.digitNotSign ∀ (sign d: Char) (more: List Char)
    (signNotDigit: Parse.isDigit sign = False)
    (digit: Parse.isDigit d = True):
    Text.stripPrefixChars [sign] [d, ..more] = None :=
  match same: Text.sameChar sign d with
    | False => byComputing
    | True =>
      let equal: sign = d := Char.ext sign d same.read
      cases

--| Digits don't start with a sign character that is not a digit.
theorem Parse.digitsNotSign ∀ (sign: Char) (digits rest: List Char)
    (some: digits ≠ [])
    (all: digits.all Parse.isDigit = True)
    (signNotDigit: Parse.isDigit sign = False):
    Text.stripPrefixChars [sign] (digits ++ rest) = None :=
  match digits with
    | [] => (some byComputing).impossible
    | [d, ..more] => Parse.digitNotSign sign d (more ++ rest) signNotDigit all.left

--| `int` on '-' and then digits, with `rest` not starting with another digit.
theorem Parse.runsIntNegative ∀ (digits rest: List Char)
    (some: digits ≠ [])
    (all: digits.all Parse.isDigit = True)
    (stops: rest.takeWhile Parse.isDigit = []):
    Parse.Runs Parse.int ['-', ..digits] rest (-(Parse.digitsValue digits).toInt) :=
  Parse.runsBind
    (() => Parse.literal { items = ['-'], same = Text.sameChar })
    (negative =>
      if negative then -(Parse.nat().toInt)
      else if Parse.literal { items = ['+'], same = Text.sameChar } then Parse.nat().toInt
      else Parse.nat().toInt)
    ['-']
    digits
    ['-', ..digits]
    rest
    True
    (-(Parse.digitsValue digits).toInt)
    byComputing
    (Parse.runsLiteral { items = ['-'], same = Text.sameChar } Text.sameCharRefl (digits ++ rest))
    (Parse.runsMap
      (() => Parse.nat().toInt)
      (i => -i)
      digits
      rest
      (Parse.digitsValue digits).toInt
      (Parse.runsMap Parse.nat
        (m => m.toInt)
        digits
        rest
        (Parse.digitsValue digits)
        (Parse.runsNat digits rest some all stops)))

--| `int` on '+' and then digits, with `rest` not starting with another digit.
theorem Parse.runsIntPositive ∀ (digits rest: List Char)
    (some: digits ≠ [])
    (all: digits.all Parse.isDigit = True)
    (stops: rest.takeWhile Parse.isDigit = []):
    Parse.Runs Parse.int ['+', ..digits] rest (Parse.digitsValue digits).toInt :=
  Parse.runsBind
    (() => Parse.literal { items = ['-'], same = Text.sameChar })
    (negative =>
      if negative then -(Parse.nat().toInt)
      else if Parse.literal { items = ['+'], same = Text.sameChar } then Parse.nat().toInt
      else Parse.nat().toInt)
    []
    ['+', ..digits]
    ['+', ..digits]
    rest
    False
    (Parse.digitsValue digits).toInt
    byComputing
    (Parse.runsLiteralAbsent { items = ['-'], same = Text.sameChar } (['+', ..digits] ++ rest) byComputing)
    (Parse.runsBind
      (() => Parse.literal { items = ['+'], same = Text.sameChar })
      (plus => if plus then Parse.nat().toInt else Parse.nat().toInt)
      ['+']
      digits
      ['+', ..digits]
      rest
      True
      (Parse.digitsValue digits).toInt
      byComputing
      (Parse.runsLiteral { items = ['+'], same = Text.sameChar } Text.sameCharRefl (digits ++ rest))
      (Parse.runsMap Parse.nat
        (m => m.toInt)
        digits
        rest
        (Parse.digitsValue digits)
        (Parse.runsNat digits rest some all stops)))

--| `int` on digits with no sign, with `rest` not starting with another digit.
theorem Parse.runsIntUnsigned ∀ (digits rest: List Char)
    (some: digits ≠ [])
    (all: digits.all Parse.isDigit = True)
    (stops: rest.takeWhile Parse.isDigit = []):
    Parse.Runs Parse.int digits rest (Parse.digitsValue digits).toInt :=
  Parse.runsBind
    (() => Parse.literal { items = ['-'], same = Text.sameChar })
    (negative =>
      if negative then -(Parse.nat().toInt)
      else if Parse.literal { items = ['+'], same = Text.sameChar } then Parse.nat().toInt
      else Parse.nat().toInt)
    []
    digits
    digits
    rest
    False
    (Parse.digitsValue digits).toInt
    byComputing
    (Parse.runsLiteralAbsent
      { items = ['-'], same = Text.sameChar }
      (digits ++ rest)
      (Eq.trans
        (Parse.stripPrefixBySameChar (digits ++ rest) ['-'])
        (Parse.digitsNotSign '-' digits rest some all byComputing)))
    (Parse.runsBind
      (() => Parse.literal { items = ['+'], same = Text.sameChar })
      (plus => if plus then Parse.nat().toInt else Parse.nat().toInt)
      []
      digits
      digits
      rest
      False
      (Parse.digitsValue digits).toInt
      byComputing
      (Parse.runsLiteralAbsent
        { items = ['+'], same = Text.sameChar }
        (digits ++ rest)
        (Eq.trans
          (Parse.stripPrefixBySameChar (digits ++ rest) ['+'])
          (Parse.digitsNotSign '+' digits rest some all byComputing)))
      (Parse.runsMap Parse.nat
        (m => m.toInt)
        digits
        rest
        (Parse.digitsValue digits)
        (Parse.runsNat digits rest some all stops)))

--| `int` on what [`Parse.IntRead`] says it reads (a '-', a '+' or no sign, then
--| digits), with `rest` not starting with another digit: it gives the number.
--| The converse of [`Parse.readsInt`].
theorem Parse.runsIntRead ∀ (read: List Char) (n: Int)
    (written: Parse.IntRead read n) (rest: List Char)
    (stops: rest.takeWhile Parse.isDigit = []):
    Parse.Runs Parse.int read rest n :=
  match written with
    | Witness digits (Both some (Both all form)) =>
      match form with
        | Inl (Both same value) => rewrite same, value then Parse.runsIntNegative digits rest some all stops
        | Inr (Inl (Both same value)) => rewrite same, value then Parse.runsIntPositive digits rest some all stops
        | Inr (Inr (Both same value)) => rewrite same, value then Parse.runsIntUnsigned digits rest some all stops

--| `withFinalLineBreak p` where there is no line break after what `p` reads (the
--| end of the line): it reads what `p` read.
theorem Parse.runsWithFinalLineBreakNone ∀ (p: () → {Parse Char} a) (read: List Char) (v: a)
    (runs: Parse.Runs p read [] v):
    Parse.Runs (() => Parse.withFinalLineBreak p) read [] v :=
  Parse.runsBind p
    (value =>
      let finalLineBreak := Parse.optional Parse.newline
      value)
    read
    []
    read
    []
    v
    v
    (List.appendNil read).flipped
    runs
    (Parse.runsBind
      (() => Parse.optional Parse.newline)
      (finalLineBreak => v)
      []
      []
      []
      []
      None
      v
      byComputing
      (Parse.declinesRuns Parse.newline [] (Parse.declinesNewline [] byComputing byComputing))
      (Parse.runsPure v []))

--| `withFinalLineBreak p` where a line break follows what `p` reads: it reads
--| that too. `p` sees the line break after it.
theorem Parse.runsWithFinalLineBreakSome ∀ (p: () → {Parse Char} a) (read lineBreak: List Char) (v: a)
    (isBreak: Parse.Runs Parse.newline lineBreak [] ())
    (runs: Parse.Runs p read lineBreak v):
    Parse.Runs (() => Parse.withFinalLineBreak p) (read ++ lineBreak) [] v :=
  Parse.runsBind p
    (value =>
      let finalLineBreak := Parse.optional Parse.newline
      value)
    read
    lineBreak
    (read ++ lineBreak)
    []
    v
    v
    byComputing
    (rewrite List.appendNil lineBreak then runs)
    (Parse.runsBind
      (() => Parse.optional Parse.newline)
      (finalLineBreak => v)
      lineBreak
      []
      lineBreak
      []
      (Some ())
      v
      (List.appendNil lineBreak).flipped
      (Parse.runsOptional Parse.newline lineBreak [] () isBreak)
      (Parse.runsPure v []))

--| `Parse.line` on a line that `withFinalLineBreak p` reads whole: it gives the
--| value. Use [`Parse.runsWithFinalLineBreakNone`] or
--| [`Parse.runsWithFinalLineBreakSome`] for the `Runs`. As [`Parse.runsEachLine`]
--| is the converse of [`Parse.eachLineReads`] for `eachLine`.
theorem Parse.runsLine ∀ (line: Text) (p: () → {Parse Char} a) (v: a)
    (runs: Parse.Runs (() => Parse.withFinalLineBreak p) line.toList [] v):
    Fail.toResult (() => Parse.line line p) = Ok v :=
  rewrite Parse.runsWhole line.toList (() => Parse.withFinalLineBreak p) v runs

--| The check `withFinalLineBreaks` makes of the line breaks at the end succeeds
--| (reading nothing) when `start` is where they begin and they are all that is
--| left, whatever they are: the last test is "no more input", which holds.
theorem Parse.runsFinalLineBreakCheck ∀ (start: Parse.Mark Char) (finalLineBreaks: List Char)
    (counted: start.left = finalLineBreaks.length):
    Parse.Runs
      (() =>
        if finalLineBreaks == [] then Parse.note (Expected "a line break")
        else if finalLineBreaks == ['\n'] then ()
        else if finalLineBreaks == ['\r', '\n'] then ()
        else if start.left == finalLineBreaks.length then ()
        else Parse.extraBlankLine start)
      []
      []
      () :=
  let holds: (start.left == finalLineBreaks.length) = True := arithmetic [counted]
  Parse.runsIf
    (finalLineBreaks == [])
    (() => Parse.note (Expected "a line break"))
    (() =>
      if finalLineBreaks == ['\n'] then ()
      else if finalLineBreaks == ['\r', '\n'] then ()
      else if start.left == finalLineBreaks.length then ()
      else Parse.extraBlankLine start)
    []
    []
    ()
    (isEmpty => Parse.runsNote (Expected "a line break") [])
    (notEmpty =>
      Parse.runsIf
        (finalLineBreaks == ['\n'])
        (() => ())
        (() =>
          if finalLineBreaks == ['\r', '\n'] then ()
          else if start.left == finalLineBreaks.length then ()
          else Parse.extraBlankLine start)
        []
        []
        ()
        (isLf => Parse.runsPure () [])
        (notLf =>
          Parse.runsIf
            (finalLineBreaks == ['\r', '\n'])
            (() => ())
            (() => if start.left == finalLineBreaks.length then () else Parse.extraBlankLine start)
            []
            []
            ()
            (isCrlf => Parse.runsPure () [])
            (notCrlf => rewrite holds then Parse.runsPure () [])))

--| What `withFinalLineBreaks` does after its parser gave `v`, where only
--| line breaks are left: it reads them and gives `v`.
theorem Parse.runsFinalLineBreaksAfter ∀ (breaks: List Char) (v: a)
    (allBreaks: breaks.all (char => char == '\n' ∨ char == '\r') = True):
    Parse.Runs
      (() =>
        let start := Parse.mark()
        let finalLineBreaks := Parse.span (char => char == '\n' ∨ char == '\r')
        if finalLineBreaks == [] then Parse.note (Expected "a line break")
        else if finalLineBreaks == ['\n'] then ()
        else if finalLineBreaks == ['\r', '\n'] then ()
        else if start.left == finalLineBreaks.length then ()
        else Parse.extraBlankLine start
        v)
      breaks
      []
      v :=
  state starts honest =>
    let starts2: state.at.rest = breaks := rewrite List.appendNil breaks at starts then starts
    let counted: state.at.left = breaks.length := rewrite starts2 at honest then honest
    Parse.runsFromMark state
      (start =>
        let finalLineBreaks := Parse.span (char => char == '\n' ∨ char == '\r')
        if finalLineBreaks == [] then Parse.note (Expected "a line break")
        else if finalLineBreaks == ['\n'] then ()
        else if finalLineBreaks == ['\r', '\n'] then ()
        else if start.left == finalLineBreaks.length then ()
        else Parse.extraBlankLine start
        v)
      breaks
      []
      v
      (Parse.runsFromBind state
        (() => Parse.span (char => char == '\n' ∨ char == '\r'))
        (finalLineBreaks =>
          if finalLineBreaks == [] then Parse.note (Expected "a line break")
          else if finalLineBreaks == ['\n'] then ()
          else if finalLineBreaks == ['\r', '\n'] then ()
          else if state.at.left == finalLineBreaks.length then ()
          else Parse.extraBlankLine state.at
          v)
        breaks
        []
        breaks
        []
        breaks
        v
        (List.appendNil breaks).flipped
        (Parse.runsSpan (char => char == '\n' ∨ char == '\r') breaks [] allBreaks byComputing)
        (middle atRest honest2 offset =>
          Parse.runsBind
            (() =>
              if breaks == [] then Parse.note (Expected "a line break")
              else if breaks == ['\n'] then ()
              else if breaks == ['\r', '\n'] then ()
              else if state.at.left == breaks.length then ()
              else Parse.extraBlankLine state.at)
            (u => v)
            []
            []
            []
            []
            ()
            v
            byComputing
            (Parse.runsFinalLineBreakCheck state.at breaks counted)
            (Parse.runsPure v [])
            middle))
      starts
      honest

--| As [`Parse.runsWithFinalLineBreaks`], from one state: for a `p` whose
--| value depends on where it starts, such as `Parse.locatedToEnd`'s
--| offsets.
theorem Parse.runsFromWithFinalLineBreaks ∀ (state: Parse.State Char) (p: () → {Parse Char} a)
    (read breaks: List Char) (v: a)
    (allBreaks: breaks.all (char => char == '\n' ∨ char == '\r') = True)
    (runs: Parse.RunsFrom state p read breaks v):
    Parse.RunsFrom state (() => Parse.withFinalLineBreaks p) (read ++ breaks) [] v :=
  Parse.runsFromBindAt state p
    (value =>
      let start := Parse.mark()
      let finalLineBreaks := Parse.span (char => char == '\n' ∨ char == '\r')
      if finalLineBreaks == [] then Parse.note (Expected "a line break")
      else if finalLineBreaks == ['\n'] then ()
      else if finalLineBreaks == ['\r', '\n'] then ()
      else if start.left == finalLineBreaks.length then ()
      else Parse.extraBlankLine start
      value)
    read
    breaks
    (read ++ breaks)
    []
    v
    v
    byComputing
    (rewrite List.appendNil breaks then runs)
    (middle atRest honest offset => Parse.runsFinalLineBreaksAfter breaks v allBreaks middle)

--| `withFinalLineBreaks p` where only line breaks (`\n` and `\r`, any number)
--| follow what `p` reads: it reads those too. `p` sees them after it.
theorem Parse.runsWithFinalLineBreaks ∀ (p: () → {Parse Char} a) (read breaks: List Char) (v: a)
    (allBreaks: breaks.all (char => char == '\n' ∨ char == '\r') = True)
    (runs: Parse.Runs p read breaks v):
    Parse.Runs (() => Parse.withFinalLineBreaks p) (read ++ breaks) [] v :=
  state => Parse.runsFromWithFinalLineBreaks state p read breaks v allBreaks (runs state)

--| `Parse.all` on input that is what `p` reads followed by line breaks only:
--| it gives the value. The converse of the `all` runner's soundness half
--| (a successful `all` gives a value `p` could give on a start of the input).
theorem Parse.runsAll ∀ (input: Text) (p: () → {Parse Char} a) (read breaks: List Char) (v: a)
    (split: input.toList = read ++ breaks)
    (allBreaks: breaks.all (char => char == '\n' ∨ char == '\r') = True)
    (runs: Parse.Runs p read breaks v):
    Fail.toResult (() => Parse.all input p) = Ok v :=
  rewrite Parse.runsWhole input.toList
    (() => Parse.withFinalLineBreaks p)
    v
    (rewrite split then Parse.runsWithFinalLineBreaks p read breaks v allBreaks runs)

--| As [`Parse.runsAll`], for a `p` whose value depends on where it starts
--| (the start of the input here): `Parse.locatedToEnd`'s offsets, say.
theorem Parse.runsFromAll ∀ (input: Text) (p: () → {Parse Char} a) (read breaks: List Char) (v: a)
    (split: input.toList = read ++ breaks)
    (allBreaks: breaks.all (char => char == '\n' ∨ char == '\r') = True)
    (runs: Parse.RunsFrom (Parse.State.start input.toList) p read breaks v):
    Fail.toResult (() => Parse.all input p) = Ok v :=
  let moved := rewrite split at runs then runs
  rewrite Parse.runsFromWhole input.toList
    (() => Parse.withFinalLineBreaks p)
    v
    (rewrite split then
      Parse.runsFromWithFinalLineBreaks (Parse.State.start (read ++ breaks)) p read breaks v allBreaks moved)

--| `newline` on a line break, "\n" or "\r\n".
theorem Parse.runsNewline ∀ (lineBreak rest: List Char)
    (isBreak: Parse.LineBreak lineBreak):
    Parse.Runs Parse.newline lineBreak rest () :=
  match isBreak with
    | Inl same => rewrite same then Parse.runsNewlineLf rest
    | Inr same => rewrite same then Parse.runsNewlineCrlf rest

--| A line break doesn't start with a space or tab, so `spaces` before one stops.
theorem Parse.lineBreakNotSpace ∀ (lineBreak rest: List Char)
    (isBreak: Parse.LineBreak lineBreak):
    (lineBreak ++ rest).takeWhile Parse.isSpace = [] :=
  match isBreak with | Inl same | Inr same => rewrite same

--| `blankLine` on a line break, spaces and tabs, and a line break.
theorem Parse.runsBlankLine ∀ (first blanks last rest: List Char)
    (firstBreak: Parse.LineBreak first)
    (spaced: blanks.all Parse.isSpace = True)
    (lastBreak: Parse.LineBreak last):
    Parse.Runs Parse.blankLine (first ++ (blanks ++ last)) rest () :=
  Parse.runsLabelWhole "a blank line"
    (() =>
      Parse.newline()
      Parse.spaces()
      Parse.newline())
    (first ++ (blanks ++ last))
    rest
    ()
    (Parse.runsBind Parse.newline
      (u =>
        Parse.spaces()
        Parse.newline())
      first
      (blanks ++ last)
      (first ++ (blanks ++ last))
      rest
      ()
      ()
      byComputing
      (Parse.runsNewline first ((blanks ++ last) ++ rest) firstBreak)
      (Parse.runsBind Parse.spaces
        (u => Parse.newline())
        blanks
        last
        (blanks ++ last)
        rest
        ()
        ()
        byComputing
        (Parse.runsSpaces blanks (last ++ rest) spaced (Parse.lineBreakNotSpace last rest lastBreak))
        (Parse.runsNewline last rest lastBreak)))

--| `blankLine` declines where `newline` does (the usual end of a list of
--| sections: the end of the input).
theorem Parse.declinesBlankLine ∀ (input: List Char)
    (declines: Parse.Declines Parse.newline input):
    Parse.Declines Parse.blankLine input :=
  Parse.declinesLabelWhole "a blank line"
    (() =>
      Parse.newline()
      Parse.spaces()
      Parse.newline())
    input
    (Parse.declinesBind Parse.newline
      (u =>
        Parse.spaces()
        Parse.newline())
      input
      declines)

--| `blankLine` declines after a line break and blanks where the next line break
--| is missing: the line isn't blank. `rest` must not continue the blanks.
theorem Parse.declinesBlankLineAfter ∀ (first blanks rest: List Char)
    (firstBreak: Parse.LineBreak first)
    (spaced: blanks.all Parse.isSpace = True)
    (stops: rest.takeWhile Parse.isSpace = [])
    (declines: Parse.Declines Parse.newline rest):
    Parse.Declines Parse.blankLine (first ++ (blanks ++ rest)) :=
  Parse.declinesLabelWhole "a blank line"
    (() =>
      Parse.newline()
      Parse.spaces()
      Parse.newline())
    (first ++ (blanks ++ rest))
    (Parse.declinesAfter Parse.newline
      (u =>
        Parse.spaces()
        Parse.newline())
      first
      (blanks ++ rest)
      ()
      (Parse.runsNewline first (blanks ++ rest) firstBreak)
      (Parse.declinesAfter Parse.spaces
        (u => Parse.newline())
        blanks
        rest
        ()
        (Parse.runsSpaces blanks rest spaced stops)
        declines))

--| `lines p` on a first value and then rounds of a line break and a value, as
--| [`Parse.runsSepBy1`]. Build the line break with [`Parse.runsNewline`] and end
--| the list with [`Parse.declinesNewline`] (the end of the input, say).
theorem Parse.runsLines ∀ (p: () → {Parse Char} a) (firstRead: List Char) (first: a)
    (steps: List (List Char, a)) (rest: List Char)
    (runsFirst: Parse.Runs p firstRead (Parse.joinReads steps ++ rest) first)
    (manyRuns: Parse.ManyRuns (() => Parse.sepStep p Parse.newline) steps rest):
    Parse.Runs
      (() => Parse.lines p)
      (firstRead ++ Parse.joinReads steps)
      rest
      (NonEmptyList.cons first (Parse.stepValues steps)) :=
  Parse.runsSepBy1 p Parse.newline firstRead first steps rest runsFirst manyRuns

--| `sections p` on a first section and then rounds of a blank line and a
--| section, as [`Parse.runsSepBy1`]. Build the blank lines with
--| [`Parse.runsBlankLine`] and end the list with [`Parse.declinesBlankLine`].
theorem Parse.runsSections ∀ (p: () → {Parse Char} a) (firstRead: List Char) (first: a)
    (steps: List (List Char, a)) (rest: List Char)
    (runsFirst: Parse.Runs p firstRead (Parse.joinReads steps ++ rest) first)
    (manyRuns: Parse.ManyRuns (() => Parse.sepStep p Parse.blankLine) steps rest):
    Parse.Runs
      (() => Parse.sections p)
      (firstRead ++ Parse.joinReads steps)
      rest
      (NonEmptyList.cons first (Parse.stepValues steps)) :=
  Parse.runsSepBy1 p Parse.blankLine firstRead first steps rest runsFirst manyRuns

--| A line break, "\n" or "\r\n", reads something.
theorem Parse.lineBreakNotEmpty ∀ (read: List Char) (u: ()) (isBreak: Parse.LineBreak read): read ≠ [] :=
  match isBreak with
    | Inl same => rewrite same then List.consNotNil '\n' []
    | Inr same => rewrite same then List.consNotNil '\r' ['\n']

--| A blank line reads something.
theorem Parse.blankLineNotEmpty ∀ (read: List Char) (u: ()) (isBlank: Parse.BlankLine read): read ≠ [] :=
  match isBlank with
    | Witness first (Witness middle (Witness last (Both split (Both firstBreak (Both spaced lastBreak))))) =>
      match first, firstBreak with
        | [], Inl impossible => Void.impossible (List.consNotNil '\n' [] impossible.flipped)
        | [], Inr impossible => Void.impossible (List.consNotNil '\r' ['\n'] impossible.flipped)
        | [char, ..others], isBreak => rewrite split then List.consNotNil char (others ++ (middle ++ last))

--| `blankLine` on what [`Parse.BlankLine`] says it reads.
theorem Parse.runsBlankLineOf ∀ (read rest: List Char)
    (isBlank: Parse.BlankLine read):
    Parse.Runs Parse.blankLine read rest () :=
  match isBlank with
    | Witness first (Witness middle (Witness last (Both split (Both firstBreak (Both spaced lastBreak))))) =>
      rewrite split then Parse.runsBlankLine first middle last rest firstBreak spaced lastBreak

--| `lines p` reads what [`Parse.SepBy`] with line breaks says was written, as
--| [`Parse.runsSepBy1Of`] with `newline` as the separator (so `runsSeparator`,
--| `separatorNotEmpty` and the look-ahead before the separator are given:
--| `afterBreak` says `valueEnd` holds after a line break).
theorem Parse.runsLinesOf ∀ (p: () → {Parse Char} a) (spec: List Char → a → Prop)
    (valueEnd: List Char → Prop) (rest: List Char)
    (runsValue: ∀ (read: List Char) (v: a) (after: List Char) => spec read v
      → valueEnd after
      → Parse.Runs p read after v)
    (afterBreak: ∀ (read after: List Char) => Parse.LineBreak read → valueEnd (read ++ after)) (restEnd: valueEnd rest)
    (declinesEnd: Parse.Declines (() => Parse.sepStep p Parse.newline) rest)
    (read: List Char) (head: a) (tail: List a)
    (written: Parse.SepBy spec (read2 u => Parse.LineBreak read2) read (NonEmptyList.cons head tail)):
    Parse.Runs (() => Parse.lines p) read rest (NonEmptyList.cons head tail) :=
  Parse.runsSepBy1Of p Parse.newline spec
    (read2 u => Parse.LineBreak read2)
    valueEnd
    rest
    runsValue
    (read2 after u isBreak => Parse.runsNewline read2 after isBreak)
    Parse.lineBreakNotEmpty
    (read2 after u isBreak => afterBreak read2 after isBreak)
    restEnd
    declinesEnd
    read
    head
    tail
    written

--| `sections p` reads what [`Parse.SepBy`] with blank lines says was written, as
--| [`Parse.runsSepBy1Of`] with `blankLine` as the separator (`afterBlank` says
--| `valueEnd` holds after a blank line).
theorem Parse.runsSectionsOf ∀ (p: () → {Parse Char} a) (spec: List Char → a → Prop)
    (valueEnd: List Char → Prop) (rest: List Char)
    (runsValue: ∀ (read: List Char) (v: a) (after: List Char) => spec read v
      → valueEnd after
      → Parse.Runs p read after v)
    (afterBlank: ∀ (read after: List Char) => Parse.BlankLine read → valueEnd (read ++ after)) (restEnd: valueEnd rest)
    (declinesEnd: Parse.Declines (() => Parse.sepStep p Parse.blankLine) rest)
    (read: List Char) (head: a) (tail: List a)
    (written: Parse.SepBy spec (read2 u => Parse.BlankLine read2) read (NonEmptyList.cons head tail)):
    Parse.Runs (() => Parse.sections p) read rest (NonEmptyList.cons head tail) :=
  Parse.runsSepBy1Of p Parse.blankLine spec
    (read2 u => Parse.BlankLine read2)
    valueEnd
    rest
    runsValue
    (read2 after u isBlank => Parse.runsBlankLineOf read2 after isBlank)
    Parse.blankLineNotEmpty
    (read2 after u isBlank => afterBlank read2 after isBlank)
    restEnd
    declinesEnd
    read
    head
    tail
    written

-- The end of a list of lines or sections: what follows the last value is line
-- breaks to the end of the input (which `Parse.all` allows), or, for lines
-- inside sections, a blank line and then the next section. A value `p` that
-- can't start with a line break, a space or a tab declines there, so the round
-- after the last value declines, which `Parse.ManyRuns` needs.

--| The text is only line feeds and carriage returns: what `Parse.all` lets
--| follow its parser.
def Parse.OnlyBreaks (input: List Char): Prop := input.all (char => char == '\n' ∨ char == '\r') = True

--| A line feed or carriage return is one or the other.
theorem Parse.lineBreakChar ∀ (char: Char) (isBreak: (char == '\n' ∨ char == '\r') = True): char = '\n' ∨ char = '\r' :=
  match isBreak with
    | Inl lf => Inl lf.read
    | Inr cr => Inr cr.read

--| Only line breaks (`\n`, `\r`) can't start what `canStart` allows, if it
--| allows neither.
theorem Parse.cannotStartAtBreaks ∀ (canStart: Char → Bool)
    (lf: canStart '\n' = False)
    (cr: canStart '\r' = False) (input: List Char)
    (only: Parse.OnlyBreaks input):
    Parse.CannotStart canStart input :=
  match input, only with
    | [], only => char more found => Void.impossible (List.consNotNil char more found.flipped)
    | [first, ..others], only => char more found =>
      rewrite <- List.consInjectiveHead found then
        match Parse.lineBreakChar first only.left with
          | Inl same => rewrite same then lf
          | Inr same => rewrite same then cr

--| A line break, "\n" or "\r\n", is followed by nothing that starts with it.
theorem Parse.cannotStartAfterBreak ∀ (canStart: Char → Bool)
    (lf: canStart '\n' = False)
    (cr: canStart '\r' = False) (lineBreak after: List Char)
    (isBreak: Parse.LineBreak lineBreak):
    Parse.CannotStart canStart (lineBreak ++ after) :=
  match isBreak with
    | Inl same => rewrite same then (char more found => rewrite <- List.consInjectiveHead found then lf)
    | Inr same => rewrite same then (char more found => rewrite <- List.consInjectiveHead found then cr)

--| A blank line, then anything, doesn't start with what `canStart` allows,
--| if it allows no line break, space or tab.
theorem Parse.cannotStartAtBlank ∀ (canStart: Char → Bool)
    (lf: canStart '\n' = False)
    (cr: canStart '\r' = False)
    (space: ∀ (char: Char) => Parse.isSpace char = True → canStart char = False) (blank more: List Char)
    (isBlank: Parse.BlankLine blank):
    Parse.CannotStart canStart (blank ++ more) :=
  match isBlank with
    | Witness first (Witness middle (Witness last (Both split (Both firstBreak (Both spaced lastBreak))))) =>
      rewrite split, List.appendAssoc first (middle ++ last) more, List.appendAssoc middle last more then
        Parse.cannotStartAfterBreak canStart lf cr first (middle ++ (last ++ more)) firstBreak

--| [`Parse.runsNat`] before an input that can't start with a digit, which is
--| `CannotStart` as the lemmas on line breaks and blank lines give it.
theorem Parse.runsNatBefore ∀ (digits rest: List Char)
    (some: digits ≠ [])
    (all: digits.all Parse.isDigit = True)
    (stops: Parse.CannotStart Parse.isDigit rest):
    Parse.Runs Parse.nat digits rest (Parse.digitsValue digits) :=
  Parse.runsNat digits rest some all (Parse.takeWhileOfCannotStart Parse.isDigit rest stops)

--| `char expected` declines where `canStart` is false of the first
--| character, if `canStart` is true of `expected`: for a separator that the
--| text after a list can't start with.
theorem Parse.declinesCharCannotStart ∀ (expected: Char) (canStart: Char → Bool)
    (allows: canStart expected = True) (rest: List Char)
    (stops: Parse.CannotStart canStart rest):
    Parse.Declines (() => Parse.char expected) rest :=
  match rest with
    | [] => Parse.declinesCharEnd expected
    | [char, ..more] =>
      Parse.declinesChar expected char more
        (match e: char == expected with
          | False => byComputing
          | True =>
            let blocked := stops char more byComputing
            Void.impossible (Bool.trueNotFalse (Eq.trans allows.flipped (rewrite e.read at blocked then blocked))))

--| Spaces and tabs, then `ys`, all pass `q`, if each space or tab does and `ys` does.
theorem Parse.allSpacesThen ∀ (q: Char → Bool)
    (spaces: ∀ (char: Char) => Parse.isSpace char = True → q char = True) (ys: List Char)
    (rest: ys.all q = True) (xs: List Char)
    (spaced: xs.all Parse.isSpace = True):
    (xs ++ ys).all q = True :=
  match xs with
    | [] => rest
    | [x, ..more] => Bool.andIntro (spaces x spaced.left) (Parse.allSpacesThen q spaces ys rest more spaced.right)

--| A parser declines on a blank line's spaces and tabs, its last line break,
--| and anything after, if it declines on any run of `q` characters followed
--| by a line feed (`declinesRun`). The run is the spaces, with a carriage
--| return if the line break is "\r\n". For a parser that `CannotStart`
--| can't help with, because its first character can be a space (a field name
--| that a colon doesn't follow, say).
theorem Parse.declinesAfterSpacesBreak ∀ (p: () → {Parse Char} a) (q: Char → Bool)
    (spaces: ∀ (char: Char) => Parse.isSpace char = True → q char = True)
    (carriageReturn: q '\r' = True)
    (declinesRun: ∀ (run more: List Char) => run.all q = True → Parse.Declines p (run ++ ['\n', ..more]))
    (middle last more: List Char)
    (spaced: middle.all Parse.isSpace = True)
    (lastBreak: Parse.LineBreak last):
    Parse.Declines p (middle ++ (last ++ more)) :=
  match lastBreak with
    | Inl same =>
      let all := Parse.allSpacesThen q spaces [] byComputing middle spaced
      rewrite same then declinesRun middle more (rewrite List.appendNil middle at all then all)
    | Inr same =>
      rewrite same, <- List.appendAssoc middle ['\r'] ['\n', ..more] then
        declinesRun (middle ++ ['\r']) more (Parse.allSpacesThen q spaces ['\r'] (rewrite carriageReturn) middle spaced)

--| What can follow a block of lines (a `lines` inside `sections`): only line
--| breaks, or a blank line and then anything.
def Parse.LinesEnd (input: List Char): Prop :=
  Parse.OnlyBreaks input ∨ ∃ (blank: List Char) => ∃ (more: List Char) => Parse.BlankLine blank ∧ input = blank ++ more

--| A blank line and then anything is a [`Parse.LinesEnd`].
theorem Parse.linesEndAfterBlank ∀ (blank after: List Char)
    (isBlank: Parse.BlankLine blank):
    Parse.LinesEnd (blank ++ after) :=
  Inr (Witness blank (Witness after (Both isBlank byComputing)))

--| Line breaks only are a [`Parse.LinesEnd`].
theorem Parse.linesEndAtBreaks ∀ (input: List Char) (only: Parse.OnlyBreaks input): Parse.LinesEnd input := Inl only

--| `canStart` is false of a [`Parse.LinesEnd`]'s first character, if it allows
--| no line break, space or tab.
theorem Parse.cannotStartAtLinesEnd ∀ (canStart: Char → Bool)
    (lf: canStart '\n' = False)
    (cr: canStart '\r' = False)
    (space: ∀ (char: Char) => Parse.isSpace char = True → canStart char = False) (input: List Char)
    (end: Parse.LinesEnd input):
    Parse.CannotStart canStart input :=
  match end with
    | Inl only => Parse.cannotStartAtBreaks canStart lf cr input only
    | Inr (Witness blank (Witness more (Both isBlank same))) =>
      rewrite same then Parse.cannotStartAtBlank canStart lf cr space blank more isBlank

--| A round of `lines p` (a line break then `p`) declines on only line breaks,
--| given that `p` declines wherever its first character can't be one `canStart`
--| allows: either the line break isn't there, or `p` finds only line breaks
--| after it.
theorem Parse.declinesLinesAtBreaks ∀ (p: () → {Parse Char} a) (canStart: Char → Bool)
    (declinesP: ∀ (input: List Char) => Parse.CannotStart canStart input → Parse.Declines p input)
    (lf: canStart '\n' = False)
    (cr: canStart '\r' = False) (input: List Char)
    (only: Parse.OnlyBreaks input):
    Parse.Declines (() => Parse.sepStep p Parse.newline) input :=
  match input with
    | [] => Parse.declinesSepStep p Parse.newline [] (Parse.declinesNewline [] byComputing byComputing)
    | [char, ..more] =>
      let only1: Parse.OnlyBreaks more := only.right
      match Parse.lineBreakChar char only.left with
        | Inl same =>
          rewrite same then
            Parse.declinesAfter Parse.newline
              (u => p())
              ['\n']
              more
              ()
              (Parse.runsNewline ['\n'] more (Inl byComputing))
              (declinesP more (Parse.cannotStartAtBreaks canStart lf cr more only1))
        | Inr same =>
          rewrite same then
            match more with
              | [] =>
                Parse.declinesSepStep p Parse.newline ['\r'] (Parse.declinesNewline ['\r'] byComputing byComputing)
              | [next, ..later] =>
                let only2: Parse.OnlyBreaks later := only1.right
                match Parse.lineBreakChar next only1.left with
                  | Inl same2 =>
                    rewrite same2 then
                      Parse.declinesAfter Parse.newline
                        (u => p())
                        ['\r', '\n']
                        later
                        ()
                        (Parse.runsNewline ['\r', '\n'] later (Inr byComputing))
                        (declinesP later (Parse.cannotStartAtBreaks canStart lf cr later only2))
                  | Inr same2 =>
                    rewrite same2 then
                      Parse.declinesSepStep p Parse.newline
                        ['\r', '\r', ..later]
                        (Parse.declinesNewline ['\r', '\r', ..later] byComputing byComputing)

--| A round of `lines p` declines at a blank line (then anything): the line break
--| is there, and `p` would start at the blank line's spaces or line break.
theorem Parse.declinesLinesAtBlank ∀ (p: () → {Parse Char} a) (canStart: Char → Bool)
    (declinesP: ∀ (input: List Char) => Parse.CannotStart canStart input → Parse.Declines p input)
    (lf: canStart '\n' = False)
    (cr: canStart '\r' = False)
    (space: ∀ (char: Char) => Parse.isSpace char = True → canStart char = False) (blank more: List Char)
    (isBlank: Parse.BlankLine blank):
    Parse.Declines (() => Parse.sepStep p Parse.newline) (blank ++ more) :=
  match isBlank with
    | Witness first (Witness middle (Witness last (Both split (Both firstBreak (Both spaced lastBreak))))) =>
      let after := middle ++ (last ++ more)
      let afterCannot: Parse.CannotStart canStart after := match middle with
        | [] => Parse.cannotStartAfterBreak canStart lf cr last more lastBreak
        | [blank1, ..others] => char rest found => rewrite <- List.consInjectiveHead found then space blank1 spaced.left
      rewrite split, List.appendAssoc first (middle ++ last) more, List.appendAssoc middle last more then
        Parse.declinesAfter Parse.newline
          (u => p())
          first
          after
          ()
          (Parse.runsNewline first after firstBreak)
          (declinesP after afterCannot)

--| A round of `lines p` declines at a [`Parse.LinesEnd`]: line breaks only, or a
--| blank line. This is the end of lines inside sections.
theorem Parse.declinesLinesAtLinesEnd ∀ (p: () → {Parse Char} a) (canStart: Char → Bool)
    (declinesP: ∀ (input: List Char) => Parse.CannotStart canStart input → Parse.Declines p input)
    (lf: canStart '\n' = False)
    (cr: canStart '\r' = False)
    (space: ∀ (char: Char) => Parse.isSpace char = True → canStart char = False) (input: List Char)
    (end: Parse.LinesEnd input):
    Parse.Declines (() => Parse.sepStep p Parse.newline) input :=
  match end with
    | Inl only => Parse.declinesLinesAtBreaks p canStart declinesP lf cr input only
    | Inr (Witness blank (Witness more (Both isBlank same))) =>
      rewrite same then Parse.declinesLinesAtBlank p canStart declinesP lf cr space blank more isBlank

--| A round of `sections p` (a blank line then `p`) after a first line break
--| `first` and only line breaks `more`: either the blank line isn't there, or
--| it is and `p` finds only line breaks after it.
theorem Parse.declinesSectionsAfterBreak ∀ (p: () → {Parse Char} a) (canStart: Char → Bool)
    (declinesP: ∀ (input: List Char) => Parse.CannotStart canStart input → Parse.Declines p input)
    (lf: canStart '\n' = False)
    (cr: canStart '\r' = False) (first: List Char)
    (isBreak: Parse.LineBreak first) (more: List Char)
    (only: Parse.OnlyBreaks more):
    Parse.Declines (() => Parse.sepStep p Parse.blankLine) (first ++ more) :=
  match more with
    | [] =>
      Parse.declinesSepStep p Parse.blankLine
        (first ++ [])
        (Parse.declinesBlankLineAfter first [] [] isBreak byComputing byComputing
          (Parse.declinesNewline [] byComputing byComputing))
    | [char, ..others] =>
      let only1: Parse.OnlyBreaks others := only.right
      match Parse.lineBreakChar char only.left with
        | Inl same =>
          rewrite same, <- List.appendAssoc first ['\n'] others then
            Parse.declinesAfter Parse.blankLine
              (u => p())
              (first ++ ['\n'])
              others
              ()
              (Parse.runsBlankLine first [] ['\n'] others isBreak byComputing (Inl byComputing))
              (declinesP others (Parse.cannotStartAtBreaks canStart lf cr others only1))
        | Inr same =>
          rewrite same then
            match others with
              | [] =>
                Parse.declinesSepStep p Parse.blankLine
                  (first ++ ['\r'])
                  (Parse.declinesBlankLineAfter first []
                    ['\r']
                    isBreak
                    byComputing
                    byComputing
                    (Parse.declinesNewline ['\r'] byComputing byComputing))
              | [next, ..later] =>
                let only2: Parse.OnlyBreaks later := only1.right
                match Parse.lineBreakChar next only1.left with
                  | Inl same2 =>
                    rewrite same2, <- List.appendAssoc first ['\r', '\n'] later then
                      Parse.declinesAfter Parse.blankLine
                        (u => p())
                        (first ++ ['\r', '\n'])
                        later
                        ()
                        (Parse.runsBlankLine first [] ['\r', '\n'] later isBreak byComputing (Inr byComputing))
                        (declinesP later (Parse.cannotStartAtBreaks canStart lf cr later only2))
                  | Inr same2 =>
                    rewrite same2 then
                      Parse.declinesSepStep p Parse.blankLine
                        (first ++ ['\r', '\r', ..later])
                        (Parse.declinesBlankLineAfter first []
                          ['\r', '\r', ..later]
                          isBreak
                          byComputing
                          byComputing
                          (Parse.declinesNewline ['\r', '\r', ..later] byComputing byComputing))

--| A round of `sections p` declines on only line breaks (the end of the input
--| that `Parse.all` allows after the last section), given that `p` declines
--| wherever its first character can't be one `canStart` allows.
theorem Parse.declinesSectionsAtBreaks ∀ (p: () → {Parse Char} a) (canStart: Char → Bool)
    (declinesP: ∀ (input: List Char) => Parse.CannotStart canStart input → Parse.Declines p input)
    (lf: canStart '\n' = False)
    (cr: canStart '\r' = False) (input: List Char)
    (only: Parse.OnlyBreaks input):
    Parse.Declines (() => Parse.sepStep p Parse.blankLine) input :=
  match input with
    | [] =>
      Parse.declinesSepStep p Parse.blankLine []
        (Parse.declinesBlankLine [] (Parse.declinesNewline [] byComputing byComputing))
    | [char, ..more] =>
      let only1: Parse.OnlyBreaks more := only.right
      match Parse.lineBreakChar char only.left with
        | Inl same =>
          rewrite same then
            Parse.declinesSectionsAfterBreak p canStart declinesP lf cr ['\n'] (Inl byComputing) more only1
        | Inr same =>
          rewrite same then
            match more with
              | [] =>
                Parse.declinesSepStep p Parse.blankLine
                  ['\r']
                  (Parse.declinesBlankLine ['\r'] (Parse.declinesNewline ['\r'] byComputing byComputing))
              | [next, ..later] =>
                match Parse.lineBreakChar next only1.left with
                  | Inl same2 =>
                    rewrite same2 then
                      Parse.declinesSectionsAfterBreak p canStart declinesP lf cr
                        ['\r', '\n']
                        (Inr byComputing)
                        later
                        only1.right
                  | Inr same2 =>
                    rewrite same2 then
                      Parse.declinesSepStep p Parse.blankLine
                        ['\r', '\r', ..later]
                        (Parse.declinesBlankLine
                          ['\r', '\r', ..later]
                          (Parse.declinesNewline ['\r', '\r', ..later] byComputing byComputing))

def Parse.RunsExamples.numbers(): {Parse Char} NonEmptyList Nat := Parse.lines Parse.nat

--| "1", a line break and "22" are `lines nat`: [1, 22].
theorem Parse.runsLinesExample: Parse.run ['1', '\n', '2', '2'] Parse.RunsExamples.numbers
      = Ok (NonEmptyList.cons 1 [22]) :=
  Parse.runsRun Parse.RunsExamples.numbers
    ['1', '\n', '2', '2']
    (NonEmptyList.cons 1 [22])
    (Parse.runsLines Parse.nat
      ['1']
      1
      [(['\n', '2', '2'], 22)]
      []
      (Parse.runsNat ['1'] ['\n', '2', '2'] (List.consNotNil '1' []) byComputing byComputing)
      (Both
        (List.consNotNil '\n' ['2', '2'])
        (Both
          (Parse.runsSepStep Parse.nat Parse.newline
            ['\n']
            ['2', '2']
            []
            22
            (Parse.runsNewline ['\n'] ['2', '2'] (Inl byComputing))
            (Parse.runsNat ['2', '2'] [] (List.consNotNil '2' ['2']) byComputing byComputing))
          (Parse.declinesSepStep Parse.nat Parse.newline [] (Parse.declinesNewline [] byComputing byComputing)))))

def Parse.RunsExamples.commas(): {Parse Char} List Nat := Parse.sepBy Parse.nat (() => Parse.char ',')

--| "4,5" is `sepBy nat (char ',')`: [4, 5].
theorem Parse.runsSepByExample: Parse.run ['4', ',', '5'] Parse.RunsExamples.commas = Ok [4, 5] :=
  Parse.runsRun Parse.RunsExamples.commas
    ['4', ',', '5']
    [4, 5]
    (Parse.runsSepBy Parse.nat
      (() => Parse.char ',')
      ['4']
      4
      [([',', '5'], 5)]
      []
      (Parse.runsNat ['4'] [',', '5'] (List.consNotNil '4' []) byComputing byComputing)
      (Both
        (List.consNotNil ',' ['5'])
        (Both
          (Parse.runsSepStep Parse.nat
            (() => Parse.char ',')
            [',']
            ['5']
            []
            5
            (Parse.runsChar ',' ['5'])
            (Parse.runsNat ['5'] [] (List.consNotNil '5' []) byComputing byComputing))
          (Parse.declinesSepStep Parse.nat (() => Parse.char ',') [] (Parse.declinesCharEnd ',')))))

--| `exactly 2 digit` on "42" gives both digits.
theorem Parse.runsExactlyExample: Parse.Runs (() => Parse.exactly 2 Parse.digit) ['4', '2'] [] [4, 2] :=
  Parse.runsExactly 2 Parse.digit
    [(['4'], 4), (['2'], 2)]
    []
    byComputing
    (Both
      (Parse.runsDigit '4' 4 ['2'] byComputing byComputing)
      (Both (Parse.runsDigit '2' 2 [] byComputing byComputing) byComputing))

--| `int` reads "-12" as -12.
theorem Parse.runsIntExample: Parse.run ['-', '1', '2'] Parse.int = Ok (-12) :=
  Parse.runsRun Parse.int
    ['-', '1', '2']
    (-12)
    (Parse.runsIntNegative ['1', '2'] [] (List.consNotNil '1' ['2']) byComputing byComputing)

--| `all` allows the line break at the end: "7\n" parses as 7.
theorem Parse.runsAllExample: Fail.toResult (() => Parse.all "7\n" Parse.nat) = Ok 7 :=
  Parse.runsAll "7\n" Parse.nat
    ['7']
    ['\n']
    7
    byComputing
    byComputing
    (Parse.runsNat ['7'] ['\n'] (List.consNotNil '7' []) byComputing byComputing)

--| `line` on "7" with no line break.
theorem Parse.runsLineExample: Fail.toResult (() => Parse.line "7" Parse.nat) = Ok 7 :=
  Parse.runsLine "7" Parse.nat 7
    (Parse.runsWithFinalLineBreakNone Parse.nat
      ['7']
      7
      (Parse.runsNat ['7'] [] (List.consNotNil '7' []) byComputing byComputing))

--| Two sections of one number each, with a blank line between.
theorem Parse.runsSectionsExample: Parse.run ['1', '\n', '\n', '2'] (() => Parse.sections Parse.nat)
      = Ok (NonEmptyList.cons 1 [2]) :=
  Parse.runsRun
    (() => Parse.sections Parse.nat)
    ['1', '\n', '\n', '2']
    (NonEmptyList.cons 1 [2])
    (Parse.runsSections Parse.nat
      ['1']
      1
      [(['\n', '\n', '2'], 2)]
      []
      (Parse.runsNat ['1'] ['\n', '\n', '2'] (List.consNotNil '1' []) byComputing byComputing)
      (Both
        (List.consNotNil '\n' ['\n', '2'])
        (Both
          (Parse.runsSepStep Parse.nat Parse.blankLine
            ['\n', '\n']
            ['2']
            []
            2
            (Parse.runsBlankLine ['\n'] [] ['\n'] ['2'] (Inl byComputing) byComputing (Inl byComputing))
            (Parse.runsNat ['2'] [] (List.consNotNil '2' []) byComputing byComputing))
          (Parse.declinesSepStep Parse.nat Parse.blankLine []
            (Parse.declinesBlankLine [] (Parse.declinesNewline [] byComputing byComputing))))))

--| `attempt` of a number says it read something.
theorem Parse.runsAttemptExample: Parse.Runs (() => Parse.attempt Parse.nat) ['5'] [] (Some (5, True)) :=
  Parse.runsAttempt Parse.nat ['5'] [] 5 (Parse.runsNat ['5'] [] (List.consNotNil '5' []) byComputing byComputing)
