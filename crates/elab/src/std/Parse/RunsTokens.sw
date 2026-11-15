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
      (Eq.sym (List.appendNil read))
      runs
      (middle atRest honest offset =>
        let sameLength: middle.at.offset - state.at.offset = read.length := omega [offset]
        Parse.runsFromMark middle
          (finish =>
            ({ value = v, offset = state.at.offset, length = finish.offset - state.at.offset }: Parse.Located a))
          []
          rest
          { value = v, offset = state.at.offset, length = read.length }
          (rewrite sameLength in Parse.runsPure _ rest middle)))

--| `Parse.tokens` where lexing all of the input gave `tokens` (as
--| `Parse.all` does, [`Parse.runsAll`]) and the parser reads all of them: it
--| gives the parser's value.
theorem Parse.runsTokens ∀ (input: Text) (lexer: () → {Parse Char} List (Parse.Located token))
    (parser: () → {Parse (Parse.Located token)} a) (tokens: List (Parse.Located token)) (v: a)
    (lexed: Fail.toResult (() => Parse.all input lexer) = Ok tokens)
    (runs: Parse.Runs parser tokens [] v):
    Fail.toResult (() => Parse.tokens input lexer parser) = Ok v :=
  rewrite Fail.toResultThen _ _, lexed, Parse.runsWhole tokens parser v runs in rfl
