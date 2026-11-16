--| What `lex` guarantees about every source it answers for.

namespace Toy.Syntax.Proofs
import Toy.Syntax (..)
import Std (DecEq, Fail, List, Parse, Result, Text)

--| If `lex source` answers with `lexed`, the slices of `source` under
--| `lexed`'s lexemes, joined in order, are `source`: the lexemes are the
--| whole source, none lost or repeated. (The tokens are made from the
--| lexemes and drop spaces and line breaks, so the claim is about the
--| lexemes, not the tokens.) It holds because `lex` checks it before it
--| answers.
theorem lexCovers ∀ (source: Text) (lexed: Lexed)
    (h: lex source = Ok lexed):
    Text.concat (lexed.lexemes.map (lexeme => cut source lexeme)) = source :=
  match e: Fail.toResult (() => Parse.all source lexemes) with
    | Ok found =>
      match c: covers source found with
        | True => rewrite <- Result.okInjective h then DecEq.sound c
