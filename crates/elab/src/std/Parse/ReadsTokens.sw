import Parse.Problem (Expected, Literal, Literals, Message)

-- What a successful token parse read, beside the soundness lemmas of
-- Parse/Reads.sw. `Parse.Reads` is about what is read, not where, so a
-- located value's offset and length are in the completeness lemmas
-- (`Parse.runsFromLocated`, Parse/RunsTokens.sw).

--| `located p` reads what `p` read, and its value is `p`'s.
theorem Parse.readsLocated ∀ (p: () → {Parse Char} a) (spec: List Char → a → Prop)
    (reads: Parse.Reads p spec):
    Parse.Reads (() => Parse.located p) (read located => spec read located.value) :=
  Parse.readsThen Parse.readsMark (startRead start startFacts =>
    Parse.readsThen reads (firstRead value firstFacts =>
      Parse.readsThen
        [p := () => Parse.mark()]
        [j := finish => ({ value, offset = start.offset, length = finish.offset - start.offset }: Parse.Located a)]
        Parse.readsMark
        (finishRead finish finishFacts =>
          Parse.readsDone
            { value, offset = start.offset, length = finish.offset - start.offset }
            (read located => spec (startRead ++ (firstRead ++ (finishRead ++ read))) located.value)
            (rewrite startFacts, finishFacts, List.appendNil firstRead in firstFacts))))

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
        (Both rfl
          (Parse.runnerOk tokens parser
            (Parse.tokensMessage input.toList tokens)
            value
            (rewrite Fail.toResultThen _ _, e at h in h)))
    | Err message => Void.exfalso (Result.errNotOk (rewrite Fail.toResultThen _ _, e at h in h))

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
