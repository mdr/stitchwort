namespace Syntax.Proofs
import Std (Bool, Char, Effect, List, Nat, Option, Parse, Result, Text, Void)
import Syntax (..)

--| `text` is lexed as one token of `kind`, alone at the start of a line with no comments around it.
def LexesAs (text: Text) (kind: Tok): Prop :=
  lex text
    = Ok {
      leaves = [{ token = { kind, text, column = 0, lineStart = True }, trivia = Trivia.empty }],
      end = Trivia.empty
    }

theorem lexesParen: LexesAs "(" LParen := byComputing
theorem lexesDef: LexesAs "def" KwDef := byComputing
theorem lexesArrow: LexesAs "→" Arrow := byComputing

--| `skip` reads exactly the characters it is asked for.
theorem runsSkip ∀ (count: Nat) (read rest: List Char)
    (counted: read.length = count):
    Parse.Runs (() => skip count) read rest () :=
  match count, read, counted with
    | Zero, [], counted => Parse.runsPure () rest
    | Zero, [first, ..others], counted => cases
    | Succ more, [], counted => cases
    | Succ more, [first, ..others], counted =>
      Parse.runsBind
        (() => Parse.next (char => True))
        (taken => skip more)
        [first]
        others
        [first, ..others]
        rest
        (Some first)
        ()
        byComputing
        (Parse.runsNext (char => True) first (others ++ rest) byComputing)
        (runsSkip more others rest (arithmetic [counted]))

--| A token of `count` characters, read from where `state` is.
theorem runsFromTokenOf ∀ (state: Parse.State Char) (kind: Tok) (count: Nat) (read rest: List Char)
    (counted: read.length = count):
    Parse.RunsFrom state (() => tokenOf kind count) read rest {
      value = TokenLexeme kind,
      offset = state.at.offset,
      length = count
    } :=
  Parse.runsFromMark state
    (from =>
      let skipped := skip count
      located (TokenLexeme kind) from)
    read
    rest
    { value = TokenLexeme kind, offset = state.at.offset, length = count }
    (Parse.runsFromBind state
      (() => skip count)
      (skipped => located (TokenLexeme kind) state.at)
      read
      []
      read
      rest
      ()
      { value = TokenLexeme kind, offset = state.at.offset, length = count }
      (List.appendNil read).flipped
      (runsSkip count read rest counted)
      (middle atRest honest offset =>
        Parse.runsFromMark middle
          (finish =>
            ({
              value = TokenLexeme kind,
              offset = state.at.offset,
              length = finish.offset - state.at.offset
            }: Parse.Located Lexeme))
          []
          rest
          { value = TokenLexeme kind, offset = state.at.offset, length = count }
          (rewrite (arithmetic [offset, counted]: middle.at.offset - state.at.offset = count) then
            Parse.runsPure _ rest middle)))

--| One token lexeme, as a list.
theorem runsFromTokenList ∀ (state: Parse.State Char) (kind: Tok) (count: Nat) (read rest: List Char)
    (counted: read.length = count):
    Parse.RunsFrom state (() => [tokenOf kind count]) read rest [
      { value = TokenLexeme kind, offset = state.at.offset, length = count }
    ] :=
  starts honest =>
    Parse.runsFromBindAt state
      (() => tokenOf kind count)
      (x => [x])
      read
      []
      read
      rest
      { value = TokenLexeme kind, offset = state.at.offset, length = count }
      [{ value = TokenLexeme kind, offset = state.at.offset, length = count }]
      (List.appendNil read).flipped
      (runsFromTokenOf state kind count read rest counted)
      (middle atRest honest1 offset =>
        Parse.runsPure [{ value = TokenLexeme kind, offset = state.at.offset, length = count }] rest middle)
      starts
      honest

theorem runsItemParen ∀ (self: Place → {Parse Char} List (Parse.Located Lexeme)) (source: Text)
    (state: Parse.State Char) (rest: List Char):
    Parse.RunsFrom state (() => item self source TopLevel) ['('] rest [
      { value = TokenLexeme LParen, offset = state.at.offset, length = 1 }
    ] :=
  Parse.runsFromMark state (from => itemOn self source TopLevel from from.rest) ['('] rest _ (starts honest =>
    rewrite starts then runsFromTokenList state LParen 1 ['('] rest byComputing starts honest)

--| `optional p` where `p` succeeds from this state: as `Parse.runsOptional`, for a `p` whose value depends on where
--| it starts.
theorem runsFromOptional ∀ (state: Parse.State Char) (p: () → {Parse Char} a) (read rest: List Char) (v: a)
    (runsP: Parse.RunsFrom state p read rest v):
    Parse.RunsFrom state (() => Parse.optional p) read rest (Some v) :=
  starts honest =>
    match runsP starts honest with
      | Witness m (Both ran (Both mrest (Both mleft moff))) =>
        Witness m
          (Both
            (Parse.runFromOptionalFromBack p
              (Effect.Always.tree (x => Std.Unit) (p ()) (Effect.alwaysUnit (p ())))
              state.at
              state
              (x => (x, Parse.mark()))
              v
              { state | at = m } _
              ran
              byComputing)
            (Both mrest (Both mleft moff)))

--| One `item`'s lexeme at a place: it reads `read` and gives the one lexeme, whatever follows is `rest`.
def ItemReads (read: List Char) (lexeme: Lexeme) (rest: List Char): Prop :=
  ∀ (self: Place → {Parse Char} List (Parse.Located Lexeme)) (source: Text) (state: Parse.State
      Char) => Parse.RunsFrom state (() => item self source TopLevel) read rest [
    { value = lexeme, offset = state.at.offset, length = read.length }
  ]

--| The lexemes of steps (what each reads, and which it is), the first at `offset`, as one-item rounds.
def roundsAt (offset: Nat): (steps: List (List Char, Lexeme)) → List (List (Parse.Located Lexeme))
  | [] => []
  | [(read, lexeme), ..steps] =>
    [[{ value = lexeme, offset, length = read.length }], ..roundsAt (offset + read.length) steps]

--| What `many (item …)` goes through: each round reads a lexeme (never none), and the last round's `item` stops.
def ItemRounds (self: Place → {Parse Char} List (Parse.Located Lexeme)) (source: Text):
    (steps: List (List Char, Lexeme)) → (rest: List Char) → Prop
  | [], rest => Parse.Declines (() => item self source TopLevel) rest
  | [(read, lexeme), ..steps], rest =>
    read ≠ [] ∧ ItemReads read lexeme (Parse.joinReads steps ++ rest) ∧ ItemRounds self source steps rest

theorem roundsShort ∀ (self: Place → {Parse Char} List (Parse.Located Lexeme)) (source: Text)
    (steps: List (List Char, Lexeme)) (rest: List Char)
    (rounds: ItemRounds self source steps rest):
    steps.length ≤ (Parse.joinReads steps).length :=
  match steps, rounds with
    | [], rounds => byComputing
    | [(read, lexeme), ..steps], Both nonEmpty (Both reads later) =>
      match read with
        | [] => (nonEmpty byComputing).impossible
        | [char, ..more] =>
          let shorter := roundsShort self source steps rest later
          arithmetic [shorter, List.lengthAppend more (Parse.joinReads steps)]

--| `manyFrom` over `item`, from a state at its `before` mark with enough fuel, after `found`: it gives the rounds.
theorem runsItemsFrom ∀ (self: Place → {Parse Char} List (Parse.Located Lexeme)) (source: Text):
    ∀ (steps: List (List Char, Lexeme)) (rest: List Char) (fuel: Nat) (found: List
      (List (Parse.Located Lexeme))) => steps.length < fuel
      → ItemRounds self source steps rest
      → ∀ (state: Parse.State Char) => Parse.RunsFrom state
        (() => Parse.manyFrom fuel (() => item self source TopLevel) found state.at)
        (Parse.joinReads steps)
        rest
        (found.reverse ++ roundsAt state.at.offset steps)
  | steps, rest, Zero, found, enough, rounds, state, starts, honest => Void.impossible (arithmetic [enough])
  | [], rest, Succ more, found, enough, declines, state, starts, honest =>
    rewrite List.appendNil found.reverse then
      (Parse.runsFromBindAt state
            (() => Parse.optionalFrom state.at (() => item self source TopLevel))
            (found2 => Parse.manyRound more (() => item self source TopLevel) found state.at found2)
            []
            []
            []
            rest
            None
            found.reverse
            byComputing
            (Parse.declinesRuns (() => item self source TopLevel) rest declines state)
            (middle atRest honest2 offset => Parse.runsPure found.reverse rest middle)) starts honest
  | [(read, lexeme), ..steps], rest, Succ more, found, enough, Both nonEmpty
      (Both reads later), state, starts, honest =>
    let short: steps.length < more := arithmetic [enough]
    let value: found.reverse
      ++ [
        [{ value = lexeme, offset = state.at.offset, length = read.length }],
        ..roundsAt (state.at.offset + read.length) steps
      ]
      = [[{ value = lexeme, offset = state.at.offset, length = read.length }], ..found].reverse
        ++ roundsAt (state.at.offset + read.length) steps :=
      rewrite List.reverseCons [{ value = lexeme, offset = state.at.offset, length = read.length }] found,
          List.appendAssoc found.reverse
            [[{ value = lexeme, offset = state.at.offset, length = read.length }]]
            (roundsAt (state.at.offset + read.length) steps)
    rewrite value then
      (Parse.runsFromBindAt state
            (() => Parse.optionalFrom state.at (() => item self source TopLevel))
            (found2 => Parse.manyRound more (() => item self source TopLevel) found state.at found2)
            read
            (Parse.joinReads steps)
            (read ++ Parse.joinReads steps)
            rest
            (Some [{ value = lexeme, offset = state.at.offset, length = read.length }])
            ([[{ value = lexeme, offset = state.at.offset, length = read.length }], ..found].reverse
              ++ roundsAt (state.at.offset + read.length) steps)
            byComputing
            (runsFromOptional state
              (() => item self source TopLevel)
              read
              (Parse.joinReads steps ++ rest) _
              (reads self source state))
            (middle atRest honest2 offset =>
              let advanced: state.at.offset < middle.at.offset := match read with
                | [] => (nonEmpty byComputing).impossible
                | [char, ..others] => arithmetic [offset]
              let same: roundsAt middle.at.offset steps = roundsAt (state.at.offset + read.length) steps :=
                rewrite offset
              rewrite <- same then
                Parse.runsFromManyRound state.at more
                  (() => item self source TopLevel)
                  found
                  [{ value = lexeme, offset = state.at.offset, length = read.length }]
                  middle
                  (Parse.joinReads steps)
                  rest
                  ([[{ value = lexeme, offset = state.at.offset, length = read.length }], ..found].reverse
                    ++ roundsAt middle.at.offset steps)
                  advanced
                  (runsItemsFrom self source steps rest more
                    [[{ value = lexeme, offset = state.at.offset, length = read.length }], ..found]
                    short
                    later
                    middle))) starts honest

theorem concatRounds ∀ (offset: Nat) (steps: List (List Char, Lexeme)):
    List.concat (roundsAt offset steps) = Parse.locatedSteps offset steps :=
  match steps with
    | [] => byComputing
    | [(read, lexeme), ..more] => rewrite concatRounds (offset + read.length) more

--| `many (item …)` from any state reads the rounds, with each lexeme's offset from the state's.
theorem runsItems ∀ (self: Place → {Parse Char} List (Parse.Located Lexeme)) (source: Text)
    (steps: List (List Char, Lexeme)) (rest: List Char)
    (rounds: ItemRounds self source steps rest) (state: Parse.State Char):
    Parse.RunsFrom state
      (() => Parse.many (() => item self source TopLevel))
      (Parse.joinReads steps)
      rest
      (roundsAt state.at.offset steps) :=
  starts honest =>
    let short := roundsShort self source steps rest rounds
    let lengths: state.at.rest.length = (Parse.joinReads steps).length + rest.length :=
      rewrite starts then List.lengthAppend (Parse.joinReads steps) rest
    Parse.runsFromMark state
      (at => Parse.manyFrom (at.left + 1) (() => item self source TopLevel) [] at)
      (Parse.joinReads steps)
      rest
      (roundsAt state.at.offset steps)
      (runsItemsFrom self source steps rest (state.at.left + 1) [] (arithmetic [short, lengths, honest]) rounds state)
      starts
      honest

--| The lexemes of a source read lexeme by lexeme to its end (`steps`, from the first character, none reading nothing):
--| the lexer's `lexemes` gives them, each at its offset. The statement `lexCovers` and `lexPrinted` stand on.
theorem lexemesOfSteps ∀ (source: Text) (steps: List (List Char, Lexeme))
    (reads: source.toList = Parse.joinReads steps)
    (rounds: ∀ (self: Place → {Parse Char} List (Parse.Located Lexeme)) => ItemRounds self source steps []):
    lexemes source = Ok (Parse.locatedSteps 0 steps) :=
  let body := (self inner => Parse.many (() => item self source inner) |> List.concat)
  let runs: Parse.RunsFrom
    (Parse.State.start source.toList)
    (() => lexemesIn source TopLevel)
    source.toList
    []
    (Parse.locatedSteps 0 steps) :=
    Parse.runsFromMark
      (Parse.State.start source.toList)
      (at => Parse.recursiveWithFuel (at.left + 1) body TopLevel)
      source.toList
      []
      (Parse.locatedSteps 0 steps)
      (Parse.runsFromBindAt
        (Parse.State.start source.toList)
        (() =>
          Parse.many (() => item (inner => Parse.recursiveWithFuel (source.toList.length) body inner) source TopLevel))
        (x => List.concat x)
        (Parse.joinReads steps)
        []
        source.toList
        []
        (roundsAt 0 steps)
        (Parse.locatedSteps 0 steps)
        (rewrite reads then (List.appendNil (Parse.joinReads steps)).flipped)
        (runsItems
          (inner => Parse.recursiveWithFuel (source.toList.length) body inner)
          source
          steps
          []
          (rounds (inner => Parse.recursiveWithFuel (source.toList.length) body inner))
          (Parse.State.start source.toList))
        (middle atRest honest3 offset =>
          rewrite concatRounds 0 steps then Parse.runsPure (Parse.locatedSteps 0 steps) [] middle))
  rewrite Parse.runsFromRun (() => lexemesIn source TopLevel) source.toList (Parse.locatedSteps 0 steps) runs
