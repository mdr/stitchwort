import Parse.Problem (Expected, Literal, Literals, Message)

-- What a successful token parse read, beside the soundness lemmas of
-- Parse/Reads.sw. `Parse.Reads` is about what is read, not where, so a
-- located value's offset and length are in the completeness lemmas
-- (`Parse.runsFromLocated`, Parse/RunsTokens.sw).

--| `located p` reads what `p` read, and its value is `p`'s.
theorem Parse.readsLocated ∀ [inv: Parse.Invariant Char] (p: () → {Parse Char} a) (spec: List Char → a → Prop)
    (reads: Parse.ReadsIn inv p spec):
    Parse.ReadsIn inv (() => Parse.located p) (read located => spec read located.value) :=
  Parse.readsThen Parse.readsMark (startRead start startFacts =>
    Parse.readsThen reads (firstRead value firstFacts =>
      Parse.readsThen Parse.readsMark (finishRead finish finishFacts =>
        Parse.readsDone
          { value, offset = start.offset, length = finish.offset - start.offset }
          (rewrite startFacts, finishFacts, List.appendNil firstRead then firstFacts))))

--| `Parse.tokens` gave a value: lexing all of the input gave the tokens
--| (`Parse.all`'s success), and the parser read all of them.
theorem Parse.tokensOk ∀ (input: Text) (lexer: () → {Parse Char} List (Parse.Located token))
    (parser: () → {Parse (Parse.Located token)} a) (value: a)
    (h: Fail.toResult (() => Parse.tokens input lexer parser) = Ok value):
    ∃ (tokens: List (Parse.Located token)) => Fail.toResult (() => Parse.all input lexer) = Ok tokens
      ∧ Parse.whole tokens parser = Ok value :=
  match e: Fail.toResult (() => Parse.all input lexer) with
    | Ok tokens =>
      Witness tokens
        (Both byComputing
          (Parse.runnerOk tokens parser
            (Parse.tokensMessage input.toList tokens)
            value
            (rewrite Fail.toResultThen _ _, e at h then h)))
    | Err message => Void.impossible (Result.errNotOk (rewrite Fail.toResultThen _ _, e at h then h))

--| `Parse.tokens` gave a value: the input is what the lexer read followed by
--| line breaks only, the lexer's reading (`lexSpec`) holds of it and the
--| tokens it gave, and the parser's (`spec`) of the tokens, all of them,
--| and the value. As [`Parse.allReads`] and [`Parse.wholeReads`], one after
--| the other.
theorem Parse.tokensReads ∀ (input: Text) (lexer: () → {Parse Char} List (Parse.Located token))
    (parser: () → {Parse (Parse.Located token)} a) (lexSpec: List Char → List (Parse.Located token) → Prop)
    (spec: List (Parse.Located token) → a → Prop) (value: a)
    (h: Fail.toResult (() => Parse.tokens input lexer parser) = Ok value)
    (readsLexer: Parse.Reads lexer lexSpec)
    (readsParser: Parse.Reads parser spec):
    ∃ (read: List Char) => ∃ (ending: List Char) => ∃ (tokens: List (Parse.Located token)) => input.toList
      = read ++ ending
      ∧ lexSpec read tokens
      ∧ ending.all (char => char == '\n' ∨ char == '\r') = True
      ∧ spec tokens value :=
  match Parse.tokensOk input lexer parser value h with
    | Witness tokens (Both lexed ran) =>
      match Parse.allReads input lexer lexSpec tokens lexed readsLexer with
        | Witness read (Witness ending (Both split (Both holds ended))) =>
          Witness read
            (Witness ending
              (Witness tokens
                (Both split (Both holds (Both ended (Parse.wholeReads tokens parser spec value readsParser ran))))))

-- What `Parse.locatedToEnd` gave when it succeeded (the converse of
-- `Parse.runsLocatedToEnd`, Parse/RunsTokens.sw).

--| What a lexeme reads, given the characters left: from every mark where
--| `inv` holds of them, `lexeme rest` reads as `spec rest` says
--| ([`Parse.ReadsAt`]). [`Parse.locatedToEnd`]'s lexeme is such a parser.
def Parse.LexemeReads (inv: Parse.Invariant Char)
    (lexeme: List Char → {Parse Char} a) (spec: List Char → List Char → a → Prop):
    Prop :=
  ∀ (start: Parse.Mark Char) => Parse.Fits Char inv start.rest
    → Parse.ReadsAt start (() => lexeme start.rest) (spec start.rest)

--| What `locatedToEnd` read, lexeme by lexeme: each step's characters
--| (never none) and value, of which `spec` holds given the characters that
--| were left when it was read (the step's own, then the later steps').
def Parse.LexemesRead (spec: List Char → List Char → a → Prop): (steps: List (List Char, a)) → Prop
  | [] => True
  | [(read, value), ..steps] =>
    read ≠ [] ∧ spec (read ++ Parse.joinReads steps) read value ∧ Parse.LexemesRead spec steps

--| `locatedToEndFrom` from a state at its `start` mark, with fuel for every
--| character left, after `found` (newest first), succeeded: it read to the
--| end, lexeme by lexeme, and gave each with its offset and length.
theorem Parse.locatedToEndFromReads ∀ [inv: Parse.Invariant Char]
    (lexeme: List Char → {Parse Char} a) (spec: List Char → List Char → a → Prop)
    (reads: Parse.LexemeReads inv lexeme spec)
    (fuel: Nat) (found: List (Parse.Located a)) (total: Nat) (state: Parse.State Char)
    (value: List (Parse.Located a)) (after: Parse.Mark Char)
    (fine: Parse.Fits Char inv state.at.rest)
    (honest: Parse.Honest total state.at)
    (enough: state.at.left < fuel)
    (h: Parse.runFrom state (() => (Parse.locatedToEndFrom fuel lexeme found state.at, Parse.mark()))
      = Ok (value, after)):
    ∃ (steps: List (List Char, a)) => state.at.rest = Parse.joinReads steps
      ∧ after.rest = []
      ∧ after.left = 0
      ∧ value = found.reverse ++ Parse.locatedSteps state.at.offset steps
      ∧ Parse.LexemesRead spec steps :=
  match fuel with
    | Succ more =>
      match e: state.at.rest with
        | [] =>
          let same := Result.okInjective h
          let valueSame: found.reverse = value := Pair.mkInjectiveFst same
          let atSame: (state.note (Expected "a token")).at = after := Pair.mkInjectiveSnd same
          Witness []
            (Both byComputing
              (Both
                (rewrite <- atSame, Parse.noteAt state (Expected "a token") then e)
                (Both
                  (rewrite <- atSame, Parse.noteAt state (Expected "a token") then arithmetic [honest.left])
                  (Both (rewrite <- valueSame, List.appendNil found.reverse) byComputing))))
        | [char, ..chars] =>
          match Parse.runFromThenOk2
            (() => lexeme state.at.rest)
            state
            (x => Parse.locatedToEndRound more lexeme found state.at x Parse.mark())
            (x => (x, Parse.mark()))
            (value, after)
            h with
            | Witness v (Witness middle (Both ran rest)) =>
              match reads state.at fine total state v middle.at byComputing honest ran with
                | Witness read1 (Both starts1 (Both honest1 holds1)) =>
                  let newest: Parse.Located a :=
                    { value = v, offset = state.at.offset, length = middle.at.offset - state.at.offset }
                  match Parse.runFromIfOk
                    (middle.at.offset > state.at.offset)
                    (() => Parse.locatedToEndFrom more lexeme [newest, ..found] middle.at)
                    (() => Empty.absurd (Parse.fatal "`locatedToEnd`: the lexeme matched without reading anything"))
                    middle
                    value
                    after
                    rest with
                    | Inr (Both isFalse noRun) => (Result.errNotOk noRun).impossible
                    | Inl (Both isTrue yesRun) =>
                      let lengths: state.at.rest.length = read1.length + middle.at.rest.length :=
                        rewrite starts1 then List.lengthAppend read1 middle.at.rest
                      let sameLength: middle.at.offset - state.at.offset = read1.length :=
                        arithmetic [honest.left, honest.right, honest1.left, honest1.right, lengths, isTrue]
                      let offsetSame: middle.at.offset = state.at.offset + read1.length :=
                        arithmetic [honest.left, honest.right, honest1.left, honest1.right, lengths, isTrue]
                      let nonEmpty: read1 ≠ [] := isNil =>
                        let zero: read1.length = 0 := rewrite isNil
                        arithmetic [zero, sameLength, isTrue]
                      match Parse.locatedToEndFromReads lexeme spec reads more
                        [newest, ..found]
                        total
                        middle
                        value
                        after
                        (fine.after (rewrite <- e then starts1))
                        honest1
                        (arithmetic [enough, honest.left, honest.right, honest1.left, honest1.right, isTrue, lengths])
                        yesRun with
                        | Witness steps (Both joined (Both empty (Both zeroLeft (Both valueSame lexemes)))) =>
                          Witness
                            [(read1, v), ..steps]
                            (Both
                              (rewrite <- joined then starts1)
                              (Both empty
                                (Both zeroLeft
                                  (Both
                                    (rewrite valueSame,
                                        List.reverseCons newest found,
                                        List.appendAssoc found.reverse
                                          [newest]
                                          (Parse.locatedSteps middle.at.offset steps),
                                        sameLength,
                                        offsetSame)
                                    (Both nonEmpty (Both (rewrite <- joined, <- starts1 then holds1) lexemes))))))

--| `locatedToEnd lexeme` succeeded, from an honest state where `inv` holds
--| of the input left: it read all that was left, lexeme by lexeme
--| (`steps`), and gave each lexeme's value with its offset and length;
--| `spec` holds of each ([`Parse.LexemesRead`]). `lexeme`, given the
--| characters left, must read as `spec` of them says ([`Parse.LexemeReads`]).
--| The converse of [`Parse.runsLocatedToEnd`].
theorem Parse.locatedToEndReads ∀ [inv: Parse.Invariant Char]
    (lexeme: List Char → {Parse Char} a) (spec: List Char → List Char → a → Prop)
    (reads: Parse.LexemeReads inv lexeme spec)
    (total: Nat) (state: Parse.State Char) (value: List (Parse.Located a)) (after: Parse.Mark Char)
    (fine: Parse.Fits Char inv state.at.rest)
    (honest: Parse.Honest total state.at)
    (h: Parse.runFrom state (() => (Parse.locatedToEnd lexeme, Parse.mark())) = Ok (value, after)):
    ∃ (steps: List (List Char, a)) => state.at.rest = Parse.joinReads steps
      ∧ after.rest = []
      ∧ after.left = 0
      ∧ value = Parse.locatedSteps state.at.offset steps
      ∧ Parse.LexemesRead spec steps :=
  Parse.locatedToEndFromReads lexeme spec reads
    (state.at.left + 1)
    []
    total
    state
    value
    after
    fine
    honest
    (arithmetic [])
    h

--| `all input (() => locatedToEnd lexeme)` gave `found`: the input is what
--| the steps read, one after another, `found` is their values with where
--| each is in the input (the first at 0), and `spec` holds of each step.
--| So the slice of the input at a lexeme's offset and length is what its
--| step read ([`Parse.locatedStepsSlices`]).
theorem Parse.allLocatedToEnd ∀ [inv: Parse.Invariant Char] (input: Text)
    (lexeme: List Char → {Parse Char} a) (spec: List Char → List Char → a → Prop)
    (reads: Parse.LexemeReads inv lexeme spec)
    (fits: Parse.Fits Char inv input.toList) (found: List (Parse.Located a))
    (h: Fail.toResult (() => Parse.all input (() => Parse.locatedToEnd lexeme)) = Ok found):
    ∃ (steps: List (List Char, a)) => input.toList = Parse.joinReads steps
      ∧ found = Parse.locatedSteps 0 steps
      ∧ Parse.LexemesRead spec steps :=
  let whole :=
    Parse.runnerOk input.toList
      (() => Parse.withFinalLineBreaks (() => Parse.locatedToEnd lexeme))
      (Parse.allMessage input.toList)
      found
      h
  match Parse.runFromThenOk
    (() => Parse.withFinalLineBreaks (() => Parse.locatedToEnd lexeme))
    (Parse.State.start input.toList)
    (v =>
      Parse.end()
      v)
    found
    whole with
    | Witness v (Witness middle (Both ran rest)) =>
      match Parse.endOk middle v found rest with
        | Both atEnd same =>
          match Parse.runFromThenOk2
            (() => Parse.locatedToEnd lexeme)
            (Parse.State.start input.toList)
            (value => Parse.withFinalLineBreaks (() => value))
            (x => (x, Parse.mark()))
            (v, middle.at)
            ran with
            | Witness v0 (Witness mid0 (Both ran0 rest0)) =>
              match Parse.locatedToEndReads lexeme spec reads input.toList.length
                (Parse.State.start input.toList)
                v0
                mid0.at
                fits
                (Both byComputing (arithmetic []))
                ran0 with
                | Witness steps (Both joined (Both empty (Both zeroLeft (Both valueSame lexemes)))) =>
                  let honest0: mid0.at.left = mid0.at.rest.length := rewrite empty, zeroLeft
                  let startsEnd: input.toList = Parse.joinReads steps ++ mid0.at.rest :=
                    rewrite empty, List.appendNil (Parse.joinReads steps) then joined
                  let fitsEnd: Parse.Fits Char inv mid0.at.rest := fits.after startsEnd
                  match Parse.readsFinalLineBreaks v0 mid0.at fitsEnd
                    (mid0.at.offset + mid0.at.left)
                    mid0
                    v
                    middle.at
                    byComputing
                    (Parse.honestOf honest0)
                    rest0 with
                    | Witness read (Both starts (Both honestAfter (Both breaks same2))) =>
                      Witness steps (Both joined (Both (rewrite <- same, same2 then valueSame) lexemes))
