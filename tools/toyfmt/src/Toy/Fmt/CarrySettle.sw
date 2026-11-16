--| What the comment walk's invariant (`Lexer`, CarryProofs.sw) becomes
--| once rule N has settled the tokens. Offsets still rise
--| (`Toy.Syntax.Proofs.settledOffsets`). `Tidy` does not hold of every
--| token: a comma's own-line comments go above the token after it, which
--| needn't start its line (`[a`, `-- c`, `, b]` puts `-- c` above `b`). It
--| holds of every token but one straight after a comma (`settledTidy`),
--| and a comma holds no comment at all (`settledBareCommas`).

namespace Toy.Fmt.Carry
import Toy.Fmt (..)
import Toy.Syntax (..)
import Toy.Syntax.Proofs (..)
import Std (And, Bool, Eq, List, Nat, Option, Pair, Parse, Result, Text, Void)

--| Each token is `Tidy`, but for one straight after a comma;
--| `afterComma` says whether the first is.
def TidyFrom (afterComma: Bool): List Tok → Prop
  | [] => True
  | [token, ..rest] => (afterComma = False → Tidy token) ∧ TidyFrom token.value.kind.isComma rest

--| A comma holds no comment.
def BareComma (token: Tok): Prop :=
  token.value.kind.isComma = True → token.value.above = [] ∧ token.value.trailing = None

theorem homedTidy ∀ (comment: Parse.Located Comment) (current: Tok) (earlier: List Tok)
    (tidy: Tidy current)
    (all: List.All Tidy earlier):
    List.All Tidy (homed comment current earlier) :=
  match earlier, all with
    | [], _ => (tidy, ())
    | [previous, ..rest], (first, others) =>
      match moves: movesPast current previous with
        | False => (tidy, first, others)
        | True => (tidy, (homedTidy comment previous rest first others))

theorem homeStepTidy ∀ (earlier: List Tok) (token: Tok)
    (tidy: Tidy token)
    (all: List.All Tidy earlier):
    List.All Tidy (homeStep earlier token) :=
  match trailing: token.value.trailing with
    | None => (tidy, all)
    | Some comment =>
      match closes: token.value.kind.isCloser || token.value.kind.isComma with
        | False => (tidy, all)
        | True => homedTidy comment token earlier tidy all

--| Rule N's first half moves trailing comments only, so it keeps `Tidy`.
theorem homeTidy ∀ (tokens earlier: List Tok)
    (all: List.All Tidy tokens)
    (before: List.All Tidy earlier):
    List.All Tidy (tokens.foldLeft earlier homeStep) :=
  match tokens, all with
    | [], _ => before
    | [token, ..rest], (tidy, others) =>
      homeTidy rest (homeStep earlier token) others (homeStepTidy earlier token tidy before)

theorem joinNothing ∀ (back: List Trivia): joinTrivia [] back = back := match back with
  | [] => byComputing
  | [first, ..rest] => byComputing

--| Rule N's second half gives own-line comments only to a token straight
--| after a comma.
theorem carryTidy ∀ (tokens: List Tok) (carried endTrivia: List Trivia) (afterComma: Bool)
    (all: List.All Tidy tokens)
    (empty: afterComma = False → carried = []):
    TidyFrom afterComma (carryForward carried tokens endTrivia).fst :=
  match tokens, all with
    | [], _ => byComputing
    | [token, ..rest], (tidy, others) =>
      match comma: token.value.kind.isComma with
        | True =>
          let later :=
            carryTidy rest
              (joinTrivia (joinTrivia carried token.value.above) (trailingTrivia token.value.trailing))
              endTrivia
              True
              others
              (wrong => (Bool.trueNotFalse wrong).impossible)
          match step: carryForward
            (joinTrivia (joinTrivia carried token.value.above) (trailingTrivia token.value.trailing))
            rest
            endTrivia with
            | (settled, end) => ((clean starts => byComputing), later)
        | False =>
          let later := carryTidy rest [] endTrivia False others (clean => byComputing)
          match step: carryForward [] rest endTrivia with
            | (settled, end) => (
              (clean =>
                let same: joinTrivia carried token.value.above = token.value.above :=
                  rewrite empty clean then joinNothing token.value.above
                rewrite same then tidy),
              later
            )

--| After rule N every token is `Tidy` but one straight after a comma:
--| what the lexer guarantees of each token, less where a comma's
--| comments went.
theorem settledTidy ∀ (lexed: Lexed) (all: List.All Tidy lexed.tokens): TidyFrom False lexed.settled.tokens :=
  let carried :=
    carryTidy
      (lexed.tokens.foldLeft [] homeStep).reverse
      []
      lexed.endTrivia
      False
      (List.allReverse Tidy (lexed.tokens.foldLeft [] homeStep) (homeTidy lexed.tokens [] all ()))
      (clean => byComputing)
  match step: carryForward [] (lexed.tokens.foldLeft [] homeStep).reverse lexed.endTrivia with
    | (tokens, endTrivia) => carried

theorem carryBare ∀ (tokens: List Tok) (carried endTrivia: List Trivia):
    List.All BareComma (carryForward carried tokens endTrivia).fst :=
  match tokens with
    | [] => ()
    | [token, ..rest] =>
      match comma: token.value.kind.isComma with
        | True =>
          let later :=
            carryBare rest
              (joinTrivia (joinTrivia carried token.value.above) (trailingTrivia token.value.trailing))
              endTrivia
          match step: carryForward
            (joinTrivia (joinTrivia carried token.value.above) (trailingTrivia token.value.trailing))
            rest
            endTrivia with
            | (settled, end) => ((isComma => (byComputing, byComputing)), later)
        | False =>
          let later := carryBare rest [] endTrivia
          match step: carryForward [] rest endTrivia with
            | (settled, end) => ((wrong => (Bool.falseNotTrue wrong).impossible), later)

--| After rule N a comma holds no comment: so a tree that keeps none for
--| its commas loses none.
theorem settledBareCommas ∀ (lexed: Lexed): List.All BareComma lexed.settled.tokens :=
  let carried := carryBare (lexed.tokens.foldLeft [] homeStep).reverse [] lexed.endTrivia
  match step: carryForward [] (lexed.tokens.foldLeft [] homeStep).reverse lexed.endTrivia with
    | (tokens, endTrivia) => carried
