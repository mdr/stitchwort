import Parse.Problem (Expected, Literal, Literals, Message)

-- Counting what was read: `Parse.Paced`, beside the soundness lemmas of
-- Parse/Reads.sw, and with it what `Parse.locatedToEnd` gave when it
-- succeeded (the converse of `Parse.runsLocatedToEnd`, Parse/RunsTokens.sw).

--| `parser` keeps count. Run from an honest state (`left` counts the items
--| in `rest`), a success leaves an honest state whose offset has moved on
--| by as many items as were read: the offset and the count of items left
--| add up to what they did. Every parser built from the operations and
--| combinators is, unless it resets to a mark of another parse.
--| [`Parse.Reads`] says what was read; this says the marks count it.
def Parse.Paced (parser: () → {Parse t} a): Prop :=
  ∀ (state: Parse.State t) (value: a) (after: Parse.Mark t) => state.at.left = state.at.rest.length
    → Parse.runFrom state (() => (parser(), Parse.mark())) = Ok (value, after)
    → after.left = after.rest.length ∧ after.offset + after.left = state.at.offset + state.at.left

theorem Parse.pacedPure ∀ [t: Type] (x: a): Parse.Paced [t := t] (() => x) := state value after honest h =>
  let same := Result.okInjective h
  let atSame: state.at = after := Pair.mkInjectiveSnd same
  rewrite <- atSame in Both honest rfl

--| `p`, then `j` of its value, keeps count when both do.
theorem Parse.pacedThen ∀ [p: () → {Parse t} a] [j: a → {Parse t} b]
    (first: Parse.Paced p)
    (rest: ∀ (v: a) => Parse.Paced (() => j v)):
    Parse.Paced (() => j (p())) :=
  state value after honest h =>
    match Parse.runFromThenOk2 p state j _ _ h with
      | Witness v (Witness middle (Both ran restRun)) =>
        match first state v middle.at honest ran with
          | Both honest1 sum1 =>
            match rest v middle value after honest1 restRun with
              | Both honest2 sum2 => Both honest2 (omega [sum1, sum2])

theorem Parse.pacedIf ∀ (c: Bool) (yes no: () → {Parse t} a)
    (pacedYes: Parse.Paced yes)
    (pacedNo: Parse.Paced no):
    Parse.Paced (() => if c then yes() else no()) :=
  match c with
    | True => pacedYes
    | False => pacedNo

theorem Parse.pacedMark ∀ [t: Type]: Parse.Paced [t := t] (() => Parse.mark()) := state value after honest h =>
  let same := Result.okInjective h
  let atSame: state.at = after := Pair.mkInjectiveSnd same
  rewrite <- atSame in Both honest rfl

theorem Parse.pacedNote ∀ [t: Type] (problem: Parse.Problem): Parse.Paced [t := t] (() => Parse.note problem) :=
  state value after honest h =>
    let same := Result.okInjective h
    let atSame: (state.note problem).at = after := Pair.mkInjectiveSnd same
    rewrite <- atSame, Parse.noteAt state problem in Both honest rfl

--| A parser that stops or fails never succeeds, so it keeps count.
theorem Parse.pacedStop ∀ [t a: Type]: Parse.Paced [t := t] [a := a] (() => Empty.absurd Parse.stop()) :=
  state value after honest h => Void.exfalso (Result.errNotOk h)

theorem Parse.pacedFatal ∀ [t a: Type] (message: Text):
    Parse.Paced [t := t] [a := a] (() => Empty.absurd (Parse.fatal message)) :=
  state value after honest h => Void.exfalso (Result.errNotOk h)

theorem Parse.pacedExpected ∀ [t a: Type] (what: Text): Parse.Paced [t := t] [a := a] (() => Parse.expected what) :=
  state value after honest h => Void.exfalso (Result.errNotOk h)

theorem Parse.pacedFail ∀ [t a: Type] (message: Text): Parse.Paced [t := t] [a := a] (() => Parse.fail message) :=
  state value after honest h => Void.exfalso (Result.errNotOk h)

theorem Parse.pacedSpan ∀ (passes: t → Bool): Parse.Paced (() => Parse.span passes) := state value after honest h =>
  let same := Result.okInjective h
  let atSame: (state.advance (state.at.rest.span passes).snd (state.at.rest.span passes).fst.length).at = after :=
    Pair.mkInjectiveSnd same
  let whole := List.takeWhileDropWhile passes state.at.rest
  let lengths: state.at.rest.length
    = (state.at.rest.takeWhile passes).length + (state.at.rest.dropWhile passes).length :=
    rewrite <- List.lengthAppend (state.at.rest.takeWhile passes) (state.at.rest.dropWhile passes), whole in rfl
  rewrite <- atSame, List.spanTakeDrop state.at.rest passes in Both (omega [honest, lengths]) (omega [honest, lengths])

theorem Parse.pacedNext ∀ (passes: t → Bool): Parse.Paced (() => Parse.next passes) := state value after honest h =>
  match e: state.at.rest with
    | [] =>
      let same := Result.okInjective h
      let atSame: state.at = after := Pair.mkInjectiveSnd same
      rewrite <- atSame in Both (rewrite e in honest) rfl
    | [char, ..more] =>
      match p: passes char with
        | True =>
          let same := Result.okInjective h
          let atSame: (state.advance more 1).at = after := Pair.mkInjectiveSnd same
          rewrite <- atSame in Both (omega [honest]) (omega [honest])
        | False =>
          let same := Result.okInjective h
          let atSame: state.at = after := Pair.mkInjectiveSnd same
          rewrite <- atSame in Both (rewrite e in honest) rfl

theorem Parse.pacedSatisfy ∀ (what: Text) (passes: t → Bool): Parse.Paced (() => Parse.satisfy what passes) :=
  Parse.pacedThen (Parse.pacedNext passes) (found =>
    match found with
      | Some char => Parse.pacedPure char
      | None => Parse.pacedExpected what)

theorem Parse.pacedChar ∀ (expected: Char): Parse.Paced (() => Parse.char expected) :=
  Parse.pacedThen (Parse.pacedSatisfy "'${expected}'" (== expected)) (char => Parse.pacedPure ())

--| `manyFrom` from a state at its `before` mark keeps count when `p` does.
theorem Parse.pacedManyFrom ∀ (p: () → {Parse t} a)
    (paced: Parse.Paced p)
    (fuel: Nat) (found: List a) (state: Parse.State t) (value: List a) (after: Parse.Mark t)
    (honest: state.at.left = state.at.rest.length)
    (h: Parse.runFrom state (() => (Parse.manyFrom fuel p found state.at, Parse.mark())) = Ok (value, after)):
    after.left = after.rest.length ∧ after.offset + after.left = state.at.offset + state.at.left :=
  match fuel with
    | Zero => Parse.pacedPure (List.reverse found) state value after honest h
    | Succ more =>
      match Parse.runFromOptionalFromOk2 p state.at state
        (found2 => Parse.manyRound more p found state.at found2)
        (x => (x, Parse.mark()))
        (value, after)
        h with
        | Inl (Witness v (Witness middle (Both ran rest))) =>
          match paced state v middle.at honest ran with
            | Both honest1 sum1 =>
              match Parse.runFromIfOk
                (middle.at.offset > state.at.offset)
                (() => Parse.manyFrom more p [v, ..found] middle.at)
                (() => Empty.absurd (Parse.fatal "`many`: the parser matched without reading anything"))
                middle
                value
                after
                rest with
                | Inl (Both isTrue yesRun) =>
                  match Parse.pacedManyFrom p paced more [v, ..found] middle value after honest1 yesRun with
                    | Both honest2 sum2 => Both honest2 (omega [sum1, sum2])
                | Inr (Both isFalse noRun) => Void.exfalso (Result.errNotOk noRun)
        | Inr (Witness middle (Both back rest)) =>
          let honest1: middle.at.left = middle.at.rest.length := rewrite back in honest
          match Parse.pacedPure (List.reverse found) middle value after honest1 rest with
            | Both honest2 sum2 => Both honest2 (rewrite <- back in sum2)

theorem Parse.pacedMany ∀ (p: () → {Parse t} a) (paced: Parse.Paced p): Parse.Paced (() => Parse.many p) :=
  state value after honest h => Parse.pacedManyFrom p paced (state.at.left + 1) [] state value after honest h

--| [`Parse.Reads`] of one state: what `parser` reads and gives when run
--| from `state`, as `spec read value`. `Parse.Reads parser spec` is this of
--| every state. For a parser that is given what it is about to read, such
--| as [`Parse.locatedToEnd`]'s lexeme: its spec can then say what was read
--| in terms of what was there.
def Parse.ReadsFrom (state: Parse.State t) (parser: () → {Parse t} a) (spec: List t → a → Prop): Prop :=
  ∀ (value: a) (after: Parse.Mark t) => state.at.left = state.at.rest.length
    → Parse.runFrom state (() => (parser(), Parse.mark())) = Ok (value, after)
    → ∃ (read: List t) => state.at.rest = read ++ after.rest ∧ after.left = after.rest.length ∧ spec read value

--| `span` from `state` reads the items it gives: the longest start of what
--| is left whose items all pass. [`Parse.readsSpan`] says only that they
--| pass.
theorem Parse.readsFromSpan ∀ (state: Parse.State t) (passes: t → Bool):
    Parse.ReadsFrom state (() => Parse.span passes) (read taken =>
      read = taken ∧ taken = state.at.rest.takeWhile passes) :=
  value after honest h =>
    let same := Result.okInjective h
    let valueSame: (state.at.rest.span passes).fst = value := Pair.mkInjectiveFst same
    let atSame: (state.advance (state.at.rest.span passes).snd (state.at.rest.span passes).fst.length).at = after :=
      Pair.mkInjectiveSnd same
    let whole := List.takeWhileDropWhile passes state.at.rest
    let lengths: state.at.rest.length
      = (state.at.rest.takeWhile passes).length + (state.at.rest.dropWhile passes).length :=
      rewrite <- List.lengthAppend (state.at.rest.takeWhile passes) (state.at.rest.dropWhile passes), whole in rfl
    Witness value
      (rewrite <- valueSame, <- atSame, List.spanTakeDrop state.at.rest passes in
        Both (Eq.sym whole) (Both (omega [honest, lengths]) (Both rfl rfl)))

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
theorem Parse.locatedToEndFromReads ∀ (lexeme: List Char → {Parse Char} a) (spec: List Char → List Char → a → Prop)
    (reads: ∀ (state: Parse.State Char) => Parse.ReadsFrom state (() => lexeme state.at.rest) (spec state.at.rest))
    (paced: ∀ (rest: List Char) => Parse.Paced (() => lexeme rest))
    (fuel: Nat) (found: List (Parse.Located a)) (state: Parse.State Char)
    (value: List (Parse.Located a)) (after: Parse.Mark Char)
    (honest: state.at.left = state.at.rest.length)
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
            (Both rfl
              (Both
                (rewrite <- atSame, Parse.noteAt state (Expected "a token") in e)
                (Both
                  (rewrite <- atSame, Parse.noteAt state (Expected "a token") in omega [honest])
                  (Both (rewrite <- valueSame, List.appendNil found.reverse in rfl) rfl))))
        | [char, ..chars] =>
          let honest0: state.at.left = state.at.rest.length := rewrite e in honest
          match Parse.runFromThenOk2
            (() => lexeme state.at.rest)
            state
            (x => Parse.locatedToEndRound more lexeme found state.at x Parse.mark())
            (x => (x, Parse.mark()))
            (value, after)
            h with
            | Witness v (Witness middle (Both ran rest)) =>
              match reads state v middle.at honest0 ran with
                | Witness read1 (Both starts1 (Both honest1 holds1)) =>
                  match paced state.at.rest state v middle.at honest0 ran with
                    | Both honestP sum =>
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
                        | Inr (Both isFalse noRun) => Void.exfalso (Result.errNotOk noRun)
                        | Inl (Both isTrue yesRun) =>
                          let lengths: state.at.rest.length = read1.length + middle.at.rest.length :=
                            rewrite starts1 in List.lengthAppend read1 middle.at.rest
                          let sameLength: middle.at.offset - state.at.offset = read1.length :=
                            omega [sum, honest0, honest1, lengths, isTrue]
                          let offsetSame: middle.at.offset = state.at.offset + read1.length :=
                            omega [sum, honest0, honest1, lengths, isTrue]
                          let nonEmpty: read1 ≠ [] := isNil =>
                            let zero: read1.length = 0 := rewrite isNil in rfl
                            omega [zero, sameLength, isTrue]
                          match Parse.locatedToEndFromReads lexeme spec reads paced more
                            [newest, ..found]
                            middle
                            value
                            after
                            honest1
                            (omega [enough, sum, isTrue, honest0, honest1, lengths])
                            yesRun with
                            | Witness steps (Both joined (Both empty (Both zeroLeft (Both valueSame lexemes)))) =>
                              Witness
                                [(read1, v), ..steps]
                                (Both
                                  (rewrite <- joined in starts1)
                                  (Both empty
                                    (Both zeroLeft
                                      (Both
                                        (rewrite valueSame,
                                            List.reverseCons newest found,
                                            List.appendAssoc found.reverse
                                              [newest]
                                              (Parse.locatedSteps middle.at.offset steps),
                                            sameLength,
                                            offsetSame in
                                          rfl)
                                        (Both nonEmpty (Both (rewrite <- joined, <- starts1 in holds1) lexemes))))))

--| `locatedToEnd lexeme` succeeded, from an honest state: it read all that
--| was left, lexeme by lexeme (`steps`), and gave each lexeme's value with
--| its offset and length; `spec` holds of each ([`Parse.LexemesRead`]).
--| `lexeme`, given the characters left, must read as `spec` of them says
--| (from each state: [`Parse.ReadsFrom`]) and keep count. The converse of [`Parse.runsLocatedToEnd`].
theorem Parse.locatedToEndReads ∀ (lexeme: List Char → {Parse Char} a) (spec: List Char → List Char → a → Prop)
    (reads: ∀ (state: Parse.State Char) => Parse.ReadsFrom state (() => lexeme state.at.rest) (spec state.at.rest))
    (paced: ∀ (rest: List Char) => Parse.Paced (() => lexeme rest))
    (state: Parse.State Char) (value: List (Parse.Located a)) (after: Parse.Mark Char)
    (honest: state.at.left = state.at.rest.length)
    (h: Parse.runFrom state (() => (Parse.locatedToEnd lexeme, Parse.mark())) = Ok (value, after)):
    ∃ (steps: List (List Char, a)) => state.at.rest = Parse.joinReads steps
      ∧ after.rest = []
      ∧ after.left = 0
      ∧ value = Parse.locatedSteps state.at.offset steps
      ∧ Parse.LexemesRead spec steps :=
  Parse.locatedToEndFromReads lexeme spec reads paced (state.at.left + 1) [] state value after honest (omega []) h

--| `all input (() => locatedToEnd lexeme)` gave `found`: the input is what
--| the steps read, one after another, `found` is their values with where
--| each is in the input (the first at 0), and `spec` holds of each step.
--| So the slice of the input at a lexeme's offset and length is what its
--| step read ([`Parse.locatedStepsSlices`]).
theorem Parse.allLocatedToEnd ∀ (input: Text)
    (lexeme: List Char → {Parse Char} a) (spec: List Char → List Char → a → Prop)
    (reads: ∀ (state: Parse.State Char) => Parse.ReadsFrom state (() => lexeme state.at.rest) (spec state.at.rest))
    (paced: ∀ (rest: List Char) => Parse.Paced (() => lexeme rest)) (found: List (Parse.Located a))
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
              match Parse.locatedToEndReads lexeme spec reads paced
                (Parse.State.start input.toList)
                v0
                mid0.at
                rfl
                ran0 with
                | Witness steps (Both joined (Both empty (Both zeroLeft (Both valueSame lexemes)))) =>
                  let honest0: mid0.at.left = mid0.at.rest.length := rewrite empty, zeroLeft in rfl
                  match Parse.readsFinalLineBreaks v0 mid0 v middle.at honest0 rest0 with
                    | Witness read (Both starts (Both honestAfter (Both breaks same2))) =>
                      Witness steps (Both joined (Both (rewrite <- same, same2 in valueSame) lexemes))
