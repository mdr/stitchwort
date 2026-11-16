import Parse.Problem (Expected, Literal, Literals, Message)

-- Completeness for tokens, beside Parse/Runs.sw.

--| `located p` where `p` reads `read` and gives `v`, from `state`: it reads
--| the same and gives `v` with `state`'s offset and `read`'s length. The
--| offset depends on where the parse is, so this is about one state
--| (`Parse.RunsFrom`), as the lemmas about `many` are.
theorem Parse.runsFromLocated ∀ (state: Parse.State Char) (p: () → {Parse Char} a) (read rest: List Char) (v: a)
    (runs: Parse.Runs p read rest v):
    Parse.RunsFrom state (() => Parse.located p) read rest {
      value = v,
      offset = state.at.offset,
      length = read.length
    } :=
  Parse.runsFromMark state
    (start =>
      let value := p()
      let finish := Parse.mark()
      { value, offset = start.offset, length = finish.offset - start.offset })
    read
    rest
    { value = v, offset = state.at.offset, length = read.length }
    (Parse.runsFromBind state p
      (value =>
        let finish := Parse.mark()
        { value, offset = state.at.offset, length = finish.offset - state.at.offset })
      read
      []
      read
      rest
      v
      { value = v, offset = state.at.offset, length = read.length }
      (List.appendNil read).flipped
      runs
      (middle atRest honest offset =>
        let sameLength: middle.at.offset - state.at.offset = read.length := arithmetic [offset]
        Parse.runsFromMark middle
          (finish =>
            ({ value = v, offset = state.at.offset, length = finish.offset - state.at.offset }: Parse.Located a))
          []
          rest
          { value = v, offset = state.at.offset, length = read.length }
          (rewrite sameLength then Parse.runsPure _ rest middle)))

--| `lexeme` reads the input lexeme by lexeme, to its end: each step's
--| characters (never none) and value, read by `lexeme` given the characters
--| left, as `Parse.locatedToEnd` calls it.
def Parse.LexemesRun (lexeme: List Char → {Parse Char} a): (steps: List (List Char, a)) → Prop
  | [] => True
  | [(read, value), ..steps] =>
    read ≠ []
      ∧ Parse.Runs (() => lexeme (read ++ Parse.joinReads steps)) read (Parse.joinReads steps) value
      ∧ Parse.LexemesRun lexeme steps

--| The steps' values with where each is read, the first at `offset`.
def Parse.locatedSteps (offset: Nat): (steps: List (List Char, a)) → List (Parse.Located a)
  | [] => []
  | [(read, value), ..steps] =>
    [{ value, offset, length = read.length }, ..Parse.locatedSteps (offset + read.length) steps]

--| Every step's place, from the first, is at or after `offset`.
theorem Parse.locatedStepsFrom ∀ (offset: Nat) (steps: List (List Char, a)):
    List.All (located => offset ≤ located.offset) (Parse.locatedSteps offset steps) :=
  match steps with
    | [] => ()
    | [(read, value), ..later] => (
      (arithmetic []),
      (List.allImplies
        (located => offset + read.length ≤ located.offset)
        (located => offset ≤ located.offset)
        (located above => arithmetic [above])
        (Parse.locatedSteps (offset + read.length) later)
        (Parse.locatedStepsFrom (offset + read.length) later))
    )

--| The steps' places rise: when every step reads something, each starts
--| before the next, so the offsets of `locatedSteps` are strictly
--| increasing.
--|
--| Proof idea: induction on the steps. The first is at `offset` and the
--| rest start at `offset + read.length`, above it since `read` is not
--| empty, and all at or after that (`locatedStepsFrom`).
theorem Parse.locatedStepsRising ∀ (offset: Nat) (steps: List (List Char, a))
    (nonEmpty: List.All (step => step.fst ≠ []) steps):
    List.Pairwise (earlier later => earlier.offset < later.offset) (Parse.locatedSteps offset steps) :=
  match steps, nonEmpty with
    | [], _ => ()
    | [(read, value), ..later], known =>
      match read, known with
        | [], known => (known.left byComputing).impossible
        | [char, ..chars], known => (
          (List.allImplies
            (located => offset + ([char, ..chars]).length ≤ located.offset)
            (located => offset < located.offset)
            (located above => arithmetic [above])
            (Parse.locatedSteps (offset + ([char, ..chars]).length) later)
            (Parse.locatedStepsFrom (offset + ([char, ..chars]).length) later)),
          (Parse.locatedStepsRising (offset + ([char, ..chars]).length) later known.right)
        )

--| The characters of the slices of `source` at the steps' places, one after
--| another, are what the steps read, when `source` is `before`, then what
--| the steps read, then `after`, and the first step is placed after
--| `before`.
theorem Parse.locatedStepsSlices ∀ (source: Text) (before: List Char) (steps: List (List Char, a)) (after: List Char)
    (made: source.toList = before ++ (Parse.joinReads steps ++ after)):
    List.concat
      ((Parse.locatedSteps before.length steps).map (located =>
        (source.slice located.offset (located.offset + located.length)).toList))
      = Parse.joinReads steps :=
  match steps with
    | [] => byComputing
    | [(read, value), ..later] =>
      let split: source.toList = before ++ (read ++ (Parse.joinReads later ++ after)) :=
        rewrite <- List.appendAssoc read (Parse.joinReads later) after then made
      let regrouped: source.toList = (before ++ read) ++ (Parse.joinReads later ++ after) :=
        rewrite List.appendAssoc before read (Parse.joinReads later ++ after) then split
      let rest := Parse.locatedStepsSlices source (before ++ read) later after regrouped
      let first := Eq.cong Text.toList (Text.sliceMiddle source before read (Parse.joinReads later ++ after) split)
      rewrite first, <- List.lengthAppend before read, rest

--| Lexemes cut from a source and joined give the source back: the slices
--| of `source` at the places of the steps that read all of it, joined, are
--| `source`. No character is lost, repeated or moved.
theorem Parse.locatedStepsCover ∀ (source: Text) (steps: List (List Char, a))
    (reads: source.toList = Parse.joinReads steps):
    Text.concat
      ((Parse.locatedSteps 0 steps).map (located => source.slice located.offset (located.offset + located.length)))
      = source :=
  let made: source.toList = [] ++ (Parse.joinReads steps ++ []) :=
    rewrite List.appendNil (Parse.joinReads steps) then reads
  let chars := Parse.locatedStepsSlices source [] steps [] made
  let mapped := List.mapMap (Parse.locatedSteps 0 steps) Text.toList (located =>
    source.slice located.offset (located.offset + located.length))
  let listed: (Text.concat
    ((Parse.locatedSteps 0 steps).map (located =>
      source.slice located.offset (located.offset + located.length)))).toList
    = source.toList :=
    rewrite Text.concatToList
          ((Parse.locatedSteps 0 steps).map (located => source.slice located.offset (located.offset + located.length))),
        mapped,
        chars then
      Eq.flipped reads
  let joined :=
    Text.concat
      ((Parse.locatedSteps 0 steps).map (located => source.slice located.offset (located.offset + located.length)))
  calc joined
    _ = Text.fromList joined.toList := Eq.flipped (Text.fromToList joined)
    _ = Text.fromList source.toList := Eq.cong Text.fromList listed
    _ = source := Text.fromToList source

--| `locatedToEndFrom` from a state at its `start` mark, with enough fuel
--| (more than the lexemes), after `found` (newest first): it gives them all.
theorem Parse.runsLocatedToEndFrom ∀ (lexeme: List Char → {Parse Char} a) (steps: List (List Char, a)) (fuel: Nat)
    (found: List (Parse.Located a)) (state: Parse.State Char)
    (runs: Parse.LexemesRun lexeme steps)
    (enough: steps.length < fuel):
    Parse.RunsFrom state
      (() => Parse.locatedToEndFrom fuel lexeme found state.at)
      (Parse.joinReads steps)
      []
      (found.reverse ++ Parse.locatedSteps state.at.offset steps) :=
  match steps, runs with
    | [], runs => starts honest =>
      match fuel with
        | Succ more =>
          let same := Parse.noteAt state (Expected "a token")
          Witness
            (state.note (Expected "a token")).at
            (Both
              (rewrite List.appendNil found.reverse, starts)
              (Both
                (rewrite same then starts)
                (Both (rewrite same then rewrite starts at honest then honest) (rewrite same))))
    | [(read, value), ..later], Both nonEmpty (Both runsLexeme runsLater) => starts honest =>
      match fuel, read with
        | Succ more, [] => (nonEmpty byComputing).impossible
        | Succ more, [char, ..chars] =>
          let whole: state.at.rest = [char, ..chars] ++ Parse.joinReads later :=
            rewrite List.appendNil ([char, ..chars] ++ Parse.joinReads later) at starts then starts
          let core :=
            Parse.runsFromBind state
              (() => lexeme state.at.rest)
              (found1 => Parse.locatedToEndRound more lexeme found state.at found1 Parse.mark())
              [char, ..chars]
              (Parse.joinReads later)
              ([char, ..chars] ++ Parse.joinReads later)
              []
              value
              (found.reverse ++ Parse.locatedSteps state.at.offset [([char, ..chars], value), ..later])
              byComputing
              (rewrite whole, List.appendNil (Parse.joinReads later) then runsLexeme)
              (middle atRest honest1 offset =>
                let moved: (middle.at.offset > state.at.offset) = True := arithmetic [offset]
                let sameLength: middle.at.offset - state.at.offset = Succ chars.length := arithmetic [offset]
                let offsetSame: middle.at.offset = state.at.offset + Succ chars.length := arithmetic [offset]
                let newest: Parse.Located a :=
                  { value, offset = state.at.offset, length = middle.at.offset - state.at.offset }
                let ih :=
                  Parse.runsLocatedToEndFrom lexeme later more [newest, ..found] middle runsLater (arithmetic [enough])
                let step: Parse.locatedToEndRound more lexeme found state.at value middle.at
                  = Parse.locatedToEndFrom more lexeme [newest, ..found] middle.at :=
                  rewrite moved
                let result: [newest, ..found].reverse ++ Parse.locatedSteps middle.at.offset later
                  = found.reverse ++ Parse.locatedSteps state.at.offset [([char, ..chars], value), ..later] :=
                  rewrite List.reverseCons newest found, List.appendAssoc found.reverse
                    [newest]
                    (Parse.locatedSteps middle.at.offset later), sameLength, offsetSame
                Parse.runsFromMark middle
                  (finish => Parse.locatedToEndRound more lexeme found state.at value finish)
                  (Parse.joinReads later)
                  []
                  (found.reverse ++ Parse.locatedSteps state.at.offset [([char, ..chars], value), ..later])
                  (rewrite step, <- result then ih))
          match core starts honest with
            | Witness m (Both ran others) => Witness m (Both (rewrite whole then ran) others)

--| An input has at least a character per lexeme (fuel for `locatedToEnd`).
theorem Parse.lexemeStepsShort ∀ (lexeme: List Char → {Parse Char} a) (steps: List (List Char, a))
    (runs: Parse.LexemesRun lexeme steps):
    steps.length ≤ (Parse.joinReads steps).length :=
  match steps, runs with
    | [], runs => byComputing
    | [(read, value), ..later], Both nonEmpty (Both runsLexeme runsLater) =>
      match read with
        | [] => (nonEmpty byComputing).impossible
        | [char, ..chars] =>
          let shorter := Parse.lexemeStepsShort lexeme later runsLater
          arithmetic [shorter, List.lengthAppend chars (Parse.joinReads later)]

--| `locatedToEnd lexeme` on input that `lexeme` reads lexeme by lexeme
--| ([`Parse.LexemesRun`]): it reads all of it and gives each lexeme's value
--| with its offset and length. About one state (`Parse.RunsFrom`), since the
--| offsets count from where the parse is.
theorem Parse.runsLocatedToEnd ∀ (lexeme: List Char → {Parse Char} a)
    (steps: List (List Char, a)) (state: Parse.State Char)
    (runs: Parse.LexemesRun lexeme steps):
    Parse.RunsFrom state
      (() => Parse.locatedToEnd lexeme)
      (Parse.joinReads steps)
      []
      (Parse.locatedSteps state.at.offset steps) :=
  starts honest =>
    let short := Parse.lexemeStepsShort lexeme steps runs
    let lengths: state.at.rest.length = (Parse.joinReads steps).length :=
      rewrite starts, List.appendNil (Parse.joinReads steps)
    Parse.runsFromMark state
      (start => Parse.locatedToEndFrom (start.left + 1) lexeme [] start)
      (Parse.joinReads steps)
      []
      (Parse.locatedSteps state.at.offset steps)
      (Parse.runsLocatedToEndFrom lexeme steps (state.at.left + 1) [] state runs (arithmetic [short, honest, lengths]))
      starts
      honest

--| `Parse.tokens` where lexing all of the input gave `tokens` (as
--| `Parse.all` does, [`Parse.runsAll`]) and the parser reads all of them: it
--| gives the parser's value.
theorem Parse.runsTokens ∀ (input: Text) (lexer: () → {Parse Char} List (Parse.Located token))
    (parser: () → {Parse (Parse.Located token)} a) (tokens: List (Parse.Located token)) (v: a)
    (lexed: Fail.toResult (() => Parse.all input lexer) = Ok tokens)
    (runs: Parse.Runs parser tokens [] v):
    Fail.toResult (() => Parse.tokens input lexer parser) = Ok v :=
  rewrite Fail.toResultThen _ _, lexed, Parse.runsWhole tokens parser v runs
