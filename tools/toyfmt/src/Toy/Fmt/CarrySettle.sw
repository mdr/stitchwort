--| What the comment walk's invariant (`Lexer`, CarryProofs.sw) becomes
--| once rule N has settled the tokens. Offsets still rise
--| (`Toy.Syntax.Proofs.settledOffsets`). `Tidy` does not hold of every
--| token: a comma's own-line comments go above the token after it, which
--| needn't start its line (`[a`, `-- c`, `, b]` puts `-- c` above `b`). It
--| holds of every token but one straight after a comma (`settledTidy`),
--| and a comma holds no comment at all (`settledBareCommas`). Together
--| they are the walk's invariant of the settled tokens (`settledFits`).

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

theorem joinNothing ∀ (back: List Trivia): joinTrivia [] back = back := cases

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

--| `TidyFrom` and bare commas, as the walk's invariant says them.
theorem settlingOf ∀ (tokens: List Tok) (afterComma: Bool)
    (tidy: TidyFrom afterComma tokens)
    (bare: List.All BareComma tokens):
    Settling tokens :=
  match tokens, tidy, bare with
    | [], _, _ => byComputing
    | [token], _, (first, _) => first
    | [token, next, ..rest], (_, later), (first, others) =>
      (first, later.left, (settlingOf [next, ..rest] token.value.kind.isComma later others))

--| Offsets that rise, as `Rising` says of tokens.
def RisingOffsets: List Nat → Prop
  | [] => True
  | [first, ..later] => List.All (other => first < other) later ∧ RisingOffsets later

theorem aboveOffsets ∀ (first: Nat) (tokens: List Tok)
    (all: List.All (other => first < other.offset) tokens):
    List.All (other => first < other) (tokens.map (token => token.offset)) :=
  match tokens, all with
    | [], _ => ()
    | [token, ..rest], (lower, others) => (lower, (aboveOffsets first rest others))

theorem offsetsAbove ∀ (first: Nat) (tokens: List Tok)
    (all: List.All (other => first < other) (tokens.map (token => token.offset))):
    List.All (other => first < other.offset) tokens :=
  match tokens, all with
    | [], _ => ()
    | [token, ..rest], (lower, others) => (lower, (offsetsAbove first rest others))

theorem risingOffsets ∀ (tokens: List Tok)
    (rising: Rising tokens):
    RisingOffsets (tokens.map (token => token.offset)) :=
  match tokens, rising with
    | [], _ => byComputing
    | [token, ..rest], (apart, later) => ((aboveOffsets token.offset rest apart), (risingOffsets rest later))

theorem offsetsRising ∀ (tokens: List Tok)
    (rising: RisingOffsets (tokens.map (token => token.offset))):
    Rising tokens :=
  match tokens, rising with
    | [], _ => byComputing
    | [token, ..rest], (apart, later) => ((offsetsAbove token.offset rest apart), (offsetsRising rest later))

--| The settled tokens of a source are what the walk assumes: rule N moves
--| comments only, so the offsets still rise (`settledOffsets`), a comma
--| holds nothing (`settledBareCommas`), and every token but one straight
--| after a comma is still `Tidy` (`settledTidy`).
theorem settledFits ∀ (source: Text) (lexed: Lexed)
    (lexes: lex source = Ok lexed):
    Parse.Fits Tok Lexer lexed.settled.tokens :=
  let fits := lexFits source lexed lexes
  let rising: RisingOffsets (lexed.settled.tokens.map (token => token.offset)) :=
    rewrite settledOffsets lexed then risingOffsets lexed.tokens fits.right
  {
    holds = (
      (settlingOf lexed.settled.tokens False (settledTidy lexed fits.left) (settledBareCommas lexed)),
      (offsetsRising lexed.settled.tokens rising)
    )
  }
