--| Rule N (`Toy.Syntax.Lexed.settled`) keeps the lexer's texts: it moves
--| comments between tokens and makes none, so tokens that are `Good`
--| stay `Good`, and the comments at the end of the file stay comments
--| (`settledGood`). The parser's walk (WalkProofs.sw) runs over the
--| settled tokens and needs this of them.

namespace Toy.Fmt.Proofs
import Toy.Syntax (..)
import Toy.Syntax.Proofs (..)
import Toy.Fmt (..)
import Toy.Doc.Proofs (IsComment)
import Std (Bool, Eq, List, Nat, Option, Parse, Text, Void)

theorem homedGood ∀ (comment: Parse.Located Comment) (current: Parse.Located Token)
    (earlier: List (Parse.Located Token))
    (fine: IsComment comment.value.text)
    (good: Good current)
    (all: List.All Good earlier):
    List.All Good (homed comment current earlier) :=
  match earlier, all with
    | [], _ => (((good.left, good.right.left, fine)), ())
    | [previous, ..rest], (first, others) =>
      match moves: movesPast current previous with
        | False => (((good.left, good.right.left, fine)), first, others)
        | True => (((good.left, good.right.left, byComputing)), (homedGood comment previous rest fine first others))

theorem homeStepGood ∀ (earlier: List (Parse.Located Token)) (token: Parse.Located Token)
    (good: Good token)
    (all: List.All Good earlier):
    List.All Good (homeStep earlier token) :=
  match trailing: token.value.trailing with
    | None => (good, all)
    | Some comment =>
      let fine: IsComment comment.value.text := good.right.right
      match closes: token.value.kind.isCloser || token.value.kind.isComma with
        | False => (good, all)
        | True => homedGood comment token earlier fine good all

theorem homeGood ∀ (tokens earlier: List (Parse.Located Token))
    (all: List.All Good tokens)
    (before: List.All Good earlier):
    List.All Good (tokens.foldLeft earlier homeStep) :=
  match tokens, all with
    | [], _ => before
    | [token, ..rest], (good, others) =>
      homeGood rest (homeStep earlier token) others (homeStepGood earlier token good before)

theorem fineAppend ∀ (front back: List Trivia)
    (fineFront: FineTrivia front)
    (fineBack: FineTrivia back):
    FineTrivia (front ++ back) :=
  match front, fineFront with
    | [], _ => fineBack
    | [OwnLine comment, ..rest], (first, others) => (first, (fineAppend rest back others fineBack))
    | [BlankLine, ..rest], others => fineAppend rest back others fineBack

theorem joinFine ∀ (front back: List Trivia)
    (fineFront: FineTrivia front)
    (fineBack: FineTrivia back):
    FineTrivia (joinTrivia front back) :=
  match last: front.last, back, fineBack with
    | Some BlankLine, [BlankLine, ..rest], fineRest => fineAppend front rest fineFront fineRest
    | Some BlankLine, [OwnLine comment, ..rest], fineBack =>
      fineAppend front [OwnLine comment, ..rest] fineFront fineBack
    | Some BlankLine, [], fineBack => fineAppend front [] fineFront fineBack
    | Some (OwnLine comment), back, fineBack => fineAppend front back fineFront fineBack
    | None, back, fineBack => fineAppend front back fineFront fineBack

theorem trailingFine ∀ (trailing: Option (Parse.Located Comment))
    (fine: FineTrailing trailing):
    FineTrivia (trailingTrivia trailing) :=
  match trailing, fine with
    | None, _ => byComputing
    | Some comment, fine => (fine, byComputing)

--| Rule N's second half hands on comments only: by induction on the
--| tokens, what a comma held joining what the next token holds.
theorem carryGood ∀ (tokens: List (Parse.Located Token)) (carried endTrivia: List Trivia)
    (all: List.All Good tokens)
    (fineCarried: FineTrivia carried)
    (fineEnd: FineTrivia endTrivia):
    List.All Good (carryForward carried tokens endTrivia).fst ∧ FineTrivia (carryForward carried tokens endTrivia).snd :=
  match tokens, all with
    | [], _ => ((), (joinFine carried endTrivia fineCarried fineEnd))
    | [token, ..rest], (good, others) =>
      let fineAbove := joinFine carried token.value.above fineCarried good.right.left
      match comma: token.value.kind.isComma with
        | True =>
          let later :=
            carryGood rest
              (joinTrivia (joinTrivia carried token.value.above) (trailingTrivia token.value.trailing))
              endTrivia
              others
              (joinFine
                (joinTrivia carried token.value.above)
                (trailingTrivia token.value.trailing)
                fineAbove
                (trailingFine token.value.trailing good.right.right))
              fineEnd
          match step: carryForward
            (joinTrivia (joinTrivia carried token.value.above) (trailingTrivia token.value.trailing))
            rest
            endTrivia with
            | (settled, end) => (((((good.left, byComputing, byComputing)), later.left)), later.right)
        | False =>
          let later := carryGood rest [] endTrivia others byComputing fineEnd
          match step: carryForward [] rest endTrivia with
            | (settled, end) => (((((good.left, fineAbove, good.right.right)), later.left)), later.right)

--| After rule N the tokens still hold the lexer's texts, and so do the
--| comments at the end of the file.
theorem settledGood ∀ (lexed: Lexed)
    (all: List.All Good lexed.tokens)
    (fineEnd: FineTrivia lexed.endTrivia):
    List.All Good lexed.settled.tokens ∧ FineTrivia lexed.settled.endTrivia :=
  let carried :=
    carryGood
      (lexed.tokens.foldLeft [] homeStep).reverse
      []
      lexed.endTrivia
      (List.allReverse Good (lexed.tokens.foldLeft [] homeStep) (homeGood lexed.tokens [] all ()))
      byComputing
      fineEnd
  match step: carryForward [] (lexed.tokens.foldLeft [] homeStep).reverse lexed.endTrivia with
    | (tokens, endTrivia) => carried
