--| What rule N (`Lexed.settled`) keeps: every comment, in the order
--| written (`settledKeepsComments`), and every token as it was but for
--| its comments (`settledSame`, `settledOffsets`). Both are facts about
--| token lists alone, with nothing of the parser or the printer.

namespace Toy.Syntax.Proofs
import Toy.Syntax (..)
import Std (Bool, Eq, List, Nat, Option, Parse)

def ownComments (trivia: List Trivia): List Comment := trivia.flatMap Trivia.comments

--| The comments of tokens listed the newest first, in the order written.
def heldBy: List (Parse.Located Token) → List Comment
  | [] => []
  | [newest, ..older] => heldBy older ++ newest.value.comments

theorem heldReversed ∀ (tokens: List (Parse.Located Token)):
    tokens.reverse.flatMap (token => token.value.comments) = heldBy tokens :=
  match tokens with
    | [] => byComputing
    | [newest, ..older] => rewrite repeatedly [List.reverseCons, List.flatMapAppend, heldReversed older, List.appendNil]

--| Trivia with no own-line comment holds no comment.
theorem noOwnLine ∀ (trivia: List Trivia) (none: hasOwnLine trivia = False): ownComments trivia = [] :=
  match trivia, none with
    | [], _ => byComputing
    | [BlankLine, ..rest], none => noOwnLine rest none

--| A comment homed is the next comment after the tokens before it and
--| the own-line comments above `current`: it moves back only past tokens
--| that hold no comment, onto one that has no trailing comment.
theorem homedHeld ∀ (comment: Parse.Located Comment)
    (current: Parse.Located Token) (earlier: List (Parse.Located Token)):
    heldBy (homed comment current earlier) = heldBy earlier ++ (ownComments current.value.above ++ [comment.value]) :=
  match earlier with
    | [] => byComputing
    | [previous, ..rest] =>
      match moves: movesPast current previous with
        | False => byComputing
        | True =>
          let none := noOwnLine current.value.above (Bool.notTrue _ (Bool.andLeft (Bool.andRight moves)))
          let bare := freeComments previous (Bool.andRight (Bool.andRight moves))
          rewrite repeatedly [homedHeld comment previous rest, none, bare, List.appendNil, List.appendAssoc]

--| A token with no trailing comment holds the comments above it.
theorem freeComments ∀ (token: Parse.Located Token)
    (free: token.value.trailing.isNone = True):
    token.value.comments = ownComments token.value.above ++ [] :=
  match trailing: token.value.trailing, free with | None, _ => byComputing

--| One more token homed holds the comments the tokens held before.
theorem homeStepHeld ∀ (earlier: List (Parse.Located Token)) (token: Parse.Located Token):
    heldBy (homeStep earlier token) = heldBy [token, ..earlier] :=
  match token with
    | { value = { kind, startsLine, column, above, trailing }, offset, length } =>
      match trailing with
        | None => byComputing
        | Some comment =>
          match closes: kind.isCloser || kind.isComma with
            | False => byComputing
            | True =>
              homedHeld comment
                { value = { kind, startsLine, column, above, trailing = Some comment }, offset, length }
                earlier

theorem homeHeld ∀ (tokens earlier: List (Parse.Located Token)):
    heldBy (tokens.foldLeft earlier homeStep) = heldBy earlier ++ tokens.flatMap (token => token.value.comments) :=
  match tokens with
    | [] => rewrite repeatedly [List.appendNil]
    | [token, ..rest] =>
      calc heldBy (rest.foldLeft (homeStep earlier token) homeStep)
        _ = heldBy (homeStep earlier token) ++ rest.flatMap (token => token.value.comments) :=
          homeHeld rest (homeStep earlier token)
        _ = (heldBy earlier ++ token.value.comments) ++ rest.flatMap (token => token.value.comments) :=
          Eq.cong
            ((held: List Comment) => held ++ rest.flatMap (token => token.value.comments))
            (homeStepHeld earlier token)
        _ = heldBy earlier ++ (token.value.comments ++ rest.flatMap (token => token.value.comments)) :=
          List.appendAssoc _ _ _

--| Joining trivia drops at most a blank line.
theorem joinOwn ∀ (front back: List Trivia):
    ownComments (joinTrivia front back) = ownComments front ++ ownComments back :=
  match last: front.last, back with
    | Some BlankLine, [BlankLine, ..rest] => rewrite repeatedly [List.flatMapAppend]
    | Some BlankLine, [] => rewrite repeatedly [List.flatMapAppend]
    | Some BlankLine, [OwnLine comment, ..rest] => rewrite repeatedly [List.flatMapAppend]
    | Some (OwnLine comment), back => rewrite repeatedly [List.flatMapAppend]
    | None, back => rewrite repeatedly [List.flatMapAppend]

theorem trailingOwn ∀ (token: Parse.Located Token):
    token.value.comments = ownComments token.value.above ++ ownComments (trailingTrivia token.value.trailing) := cases

--| What a comma held is carried to the next token, or to the end: the
--| comments after carrying are those carried in, the tokens' and the
--| end's, in that order.
theorem carryHeld ∀ (tokens: List (Parse.Located Token)) (carried endTrivia: List Trivia):
    (carryForward carried tokens endTrivia).fst.flatMap (token => token.value.comments)
      ++ ownComments (carryForward carried tokens endTrivia).snd
      = ownComments carried ++ (tokens.flatMap (token => token.value.comments) ++ ownComments endTrivia) :=
  match tokens with
    | [] => joinOwn carried endTrivia
    | [token, ..rest] =>
      match comma: token.value.kind.isComma with
        | True =>
          let later :=
            carryHeld rest
              (joinTrivia (joinTrivia carried token.value.above) (trailingTrivia token.value.trailing))
              endTrivia
          match step: carryForward
            (joinTrivia (joinTrivia carried token.value.above) (trailingTrivia token.value.trailing))
            rest
            endTrivia with
            | (settled, end) => rewrite repeatedly [later, joinOwn, trailingOwn token, List.appendAssoc]
        | False =>
          let later := carryHeld rest [] endTrivia
          match step: carryForward [] rest endTrivia with
            | (settled, end) => rewrite repeatedly [List.appendAssoc, later, joinOwn]

--| Rule N loses no comment and keeps their order: the settled tokens
--| hold the comments the lexer found, as `Lexed.comments` lists them.
--|
--| Proof idea: a comment moves back only past tokens that hold none, onto
--| a token with no trailing comment (`homedHeld`), and what a comma holds
--| goes to the front of the next token's comments (`carryHeld`).
theorem settledKeepsComments ∀ (lexed: Lexed): lexed.settled.comments = lexed.comments :=
  let carried := carryHeld (lexed.tokens.foldLeft [] homeStep).reverse [] lexed.endTrivia
  match step: carryForward [] (lexed.tokens.foldLeft [] homeStep).reverse lexed.endTrivia with
    | (tokens, endTrivia) => rewrite repeatedly [carried, heldReversed, homeHeld lexed.tokens []]

-- The tokens stay as they were, but for their comments.

theorem homedSame ∀ (shape: Parse.Located Token → b)
    (blind: ∀ (token: Parse.Located Token) (trailing: Option (Parse.Located Comment)) => shape
      (trailingSet token trailing)
      = shape token)
    (comment: Parse.Located Comment) (current: Parse.Located Token) (earlier: List (Parse.Located Token)):
    (homed comment current earlier).map shape = [current, ..earlier].map shape :=
  match earlier with
    | [] => rewrite repeatedly [blind current (Some comment)]
    | [previous, ..rest] =>
      match moves: movesPast current previous with
        | False => rewrite repeatedly [blind current (Some comment)]
        | True => rewrite repeatedly [blind current None, homedSame shape blind comment previous rest]

theorem homeStepSame ∀ (shape: Parse.Located Token → b)
    (blind: ∀ (token: Parse.Located Token) (trailing: Option (Parse.Located Comment)) => shape
      (trailingSet token trailing)
      = shape token)
    (earlier: List (Parse.Located Token)) (token: Parse.Located Token):
    (homeStep earlier token).map shape = [token, ..earlier].map shape :=
  match trailing: token.value.trailing with
    | None => byComputing
    | Some comment =>
      match closes: token.value.kind.isCloser || token.value.kind.isComma with
        | False => byComputing
        | True => homedSame shape blind comment token earlier

theorem homeFoldSame ∀ (shape: Parse.Located Token → b)
    (blind: ∀ (token: Parse.Located Token) (trailing: Option (Parse.Located Comment)) => shape
      (trailingSet token trailing)
      = shape token) (tokens earlier: List (Parse.Located Token)):
    (tokens.foldLeft earlier homeStep).map shape = tokens.reverse.map shape ++ earlier.map shape :=
  match tokens with
    | [] => byComputing
    | [token, ..rest] =>
      rewrite repeatedly [
        homeFoldSame shape blind rest (homeStep earlier token),
        homeStepSame shape blind earlier token,
        List.reverseCons,
        List.mapAppend,
        List.appendAssoc
      ]

--| Rule N's first half changes no token but in its comments.
theorem homeSame ∀ (shape: Parse.Located Token → b)
    (blind: ∀ (token: Parse.Located Token) (trailing: Option (Parse.Located Comment)) => shape
      (trailingSet token trailing)
      = shape token) (tokens: List (Parse.Located Token)):
    (tokens.foldLeft [] homeStep).reverse.map shape = tokens.map shape :=
  calc (tokens.foldLeft [] homeStep).reverse.map shape
    _ = ((tokens.foldLeft [] homeStep).map shape).reverse := List.mapReverse (tokens.foldLeft [] homeStep) shape
    _ = (tokens.reverse.map shape ++ []).reverse :=
      Eq.cong ((mapped: List b) => mapped.reverse) (homeFoldSame shape blind tokens [])
    _ = (tokens.reverse.map shape).reverse :=
      Eq.cong ((mapped: List b) => mapped.reverse) (List.appendNil (tokens.reverse.map shape))
    _ = (tokens.map shape).reverse.reverse :=
      Eq.cong ((mapped: List b) => mapped.reverse) (List.mapReverse tokens shape)
    _ = tokens.map shape := List.reverseReverse (tokens.map shape)

--| Rule N's second half changes no token but in its comments.
theorem carrySame ∀ (shape: Parse.Located Token → b)
    (blind: ∀ (token: Parse.Located Token) (trailing: Option (Parse.Located Comment)) => shape
      (trailingSet token trailing)
      = shape token)
    (blindAbove: ∀ (token: Parse.Located Token) (above: List Trivia) => shape (aboveSet token above) = shape token)
    (tokens: List (Parse.Located Token)) (carried endTrivia: List Trivia):
    (carryForward carried tokens endTrivia).fst.map shape = tokens.map shape :=
  match tokens with
    | [] => byComputing
    | [token, ..rest] =>
      match comma: token.value.kind.isComma with
        | True =>
          let later :=
            carrySame shape blind blindAbove rest
              (joinTrivia (joinTrivia carried token.value.above) (trailingTrivia token.value.trailing))
              endTrivia
          match step: carryForward
            (joinTrivia (joinTrivia carried token.value.above) (trailingTrivia token.value.trailing))
            rest
            endTrivia with
            | (settled, end) => rewrite repeatedly [later, blind (aboveSet token []) None, blindAbove token []]
        | False =>
          let later := carrySame shape blind blindAbove rest [] endTrivia
          match step: carryForward [] rest endTrivia with
            | (settled, end) => rewrite repeatedly [later, blindAbove token (joinTrivia carried token.value.above)]

--| After rule N the tokens are the same tokens: whatever is read of a
--| token without looking at its comments (`shape`) reads the same of the
--| settled tokens, in the same order.
theorem settledSame ∀ (shape: Parse.Located Token → b)
    (blind: ∀ (token: Parse.Located Token) (trailing: Option (Parse.Located Comment)) => shape
      (trailingSet token trailing)
      = shape token)
    (blindAbove: ∀ (token: Parse.Located Token) (above: List Trivia) => shape (aboveSet token above) = shape token)
    (lexed: Lexed):
    lexed.settled.tokens.map shape = lexed.tokens.map shape :=
  let carried := carrySame shape blind blindAbove (lexed.tokens.foldLeft [] homeStep).reverse [] lexed.endTrivia
  match step: carryForward [] (lexed.tokens.foldLeft [] homeStep).reverse lexed.endTrivia with
    | (tokens, endTrivia) => Eq.trans carried (homeSame shape blind lexed.tokens)

--| A token without its comments.
def bare (token: Parse.Located Token): Parse.Located Token := trailingSet (aboveSet token []) None

--| After rule N, the tokens are the same tokens at the same places: only
--| comments moved.
theorem settledBare ∀ (lexed: Lexed): lexed.settled.tokens.map bare = lexed.tokens.map bare :=
  settledSame bare (token trailing => byComputing) (token above => byComputing) lexed

theorem settledOffsets ∀ (lexed: Lexed):
    lexed.settled.tokens.map (token => token.offset) = lexed.tokens.map (token => token.offset) :=
  settledSame (token => token.offset) (token trailing => byComputing) (token above => byComputing) lexed

--| The lexemes are the lexer's: rule N reads tokens only.
theorem settledLexemes ∀ (lexed: Lexed): lexed.settled.lexemes = lexed.lexemes := byComputing

-- Tokens rule N leaves as they are: the printer's.

--| Rule N's first half leaves `current` where it is after `earlier`
--| (newest first): its trailing comment doesn't move back.
def Steady (current: Parse.Located Token) (earlier: List (Parse.Located Token)): Prop :=
  homeStep earlier current = [current, ..earlier]

--| Rule N's first half moves no comment of these tokens (newest first).
def Stable: List (Parse.Located Token) → Prop
  | [] => True
  | [newest, ..earlier] => Steady newest earlier ∧ Stable earlier

--| A comma that holds no comment.
def BareComma (token: Parse.Located Token): Prop :=
  token.value.kind.isComma = True → token.value.above = [] ∧ token.value.trailing = None

theorem homeStable ∀ (newest: List (Parse.Located Token))
    (stable: Stable newest):
    newest.reverse.foldLeft [] homeStep = newest :=
  match newest, stable with
    | [], _ => byComputing
    | [token, ..earlier], (steady, others) =>
      calc [token, ..earlier].reverse.foldLeft [] homeStep
        _ = (earlier.reverse ++ [token]).foldLeft [] homeStep :=
          Eq.cong ((tokens: List (Parse.Located Token)) => tokens.foldLeft [] homeStep) (List.reverseCons token earlier)
        _ = homeStep (earlier.reverse.foldLeft [] homeStep) token :=
          List.foldLeftAppend earlier.reverse [] [token] homeStep
        _ = homeStep earlier token :=
          Eq.cong ((found: List (Parse.Located Token)) => homeStep found token) (homeStable earlier others)
        _ = [token, ..earlier] := steady

theorem joinEmpty ∀ (back: List Trivia): joinTrivia [] back = back := cases

--| Rule N's second half changes nothing where no comma holds a comment:
--| by induction on the tokens, nothing being carried.
theorem carryStable ∀ (tokens: List (Parse.Located Token)) (endTrivia: List Trivia)
    (bare: List.All BareComma tokens):
    carryForward [] tokens endTrivia = (tokens, endTrivia) :=
  match tokens, bare with
    | [], _ => rewrite joinEmpty endTrivia
    | [{ value = { kind, startsLine, column, above, trailing }, offset, length }, ..rest], (first, others) =>
      match comma: kind.isComma with
        | True =>
          let (noAbove, noTrailing) := first byComputing
          rewrite noAbove, noTrailing, carryStable rest endTrivia others
        | False => rewrite joinEmpty above, carryStable rest endTrivia others

--| Rule N changes nothing of tokens it has nothing to move in: no
--| trailing comment that would go back (`Stable`), no comma holding a
--| comment.
theorem settledStable ∀ (lexed: Lexed) (newest: List (Parse.Located Token))
    (same: lexed.tokens = newest.reverse)
    (stable: Stable newest)
    (bare: List.All BareComma newest):
    lexed.settled.tokens = lexed.tokens ∧ lexed.settled.endTrivia = lexed.endTrivia :=
  let homed: lexed.tokens.foldLeft [] homeStep = newest := rewrite same then homeStable newest stable
  let carried: carryForward [] newest.reverse lexed.endTrivia = (newest.reverse, lexed.endTrivia) :=
    carryStable newest.reverse lexed.endTrivia (List.allReverse BareComma newest bare)
  rewrite homed, carried, same then (byComputing, byComputing)

--| Rule N on tokens whose first half leaves no comma holding a comment:
--| the second half changes nothing, so the settled tokens are the first
--| half's.
theorem settledHomed ∀ (lexed: Lexed) (newest: List (Parse.Located Token))
    (same: lexed.tokens = newest.reverse)
    (bare: List.All BareComma (newest.reverse.foldLeft [] homeStep)):
    lexed.settled.tokens = (newest.reverse.foldLeft [] homeStep).reverse ∧ lexed.settled.endTrivia = lexed.endTrivia :=
  let carried: carryForward [] (newest.reverse.foldLeft [] homeStep).reverse lexed.endTrivia
    = ((newest.reverse.foldLeft [] homeStep).reverse, lexed.endTrivia) :=
    carryStable
      (newest.reverse.foldLeft [] homeStep).reverse
      lexed.endTrivia
      (List.allReverse BareComma (newest.reverse.foldLeft [] homeStep) bare)
  rewrite same, carried then (byComputing, byComputing)
