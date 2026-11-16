--| Tokens against events: the tokens the printed text lexes to, without
--| their offsets, are a function of the printer's trace alone
--| (`placedViews`). With `parsedPrintTokens` and `parsedPrintEvents` this
--| says what a parsed file's printed text lexes to, at every width, from
--| the file's events: each token's kind, whether it starts its line and at
--| which column, the comments and blank lines above it and the comment
--| after it. `DirectProofs` uses the three together.

namespace Toy.Fmt.Proofs
import Toy.Doc (..)
import Toy.Doc.Proofs (..)
import Toy.Syntax (..)
import Toy.Syntax.Proofs (..)
import Toy.Fmt (..)
import Std (Bool, DecEq, Eq, List, Nat, Option, Parse, Result, Text, Void)

--| A token as the parser reads it, without its offsets: `start` is its
--| column if it starts its line (the parser asks the column of no other
--| token), `trailing` the comment after it.
type TokenView = {
  kind: Kind,
  start: Option Nat,
  above: List Trivia,
  trailing: Option Comment
}

def commentOf: Option (Parse.Located Comment) → Option Comment
  | None => None
  | Some located => Some located.value

def viewOf (token: Parse.Located Token): TokenView := {
  kind = token.value.kind,
  start = if token.value.startsLine then Some token.value.column else None,
  above = token.value.above,
  trailing = commentOf token.value.trailing
}

--| Tokens' views (newest first) and the trivia waiting for the next
--| token (newest first).
type Views = { views: List TokenView, pending: List Trivia }

def Placed.views (placed: Placed): Views := { views = placed.tokens.map viewOf, pending = placed.pending }

def viewTrailing (views: List TokenView) (comment: Comment): List TokenView := match views with
  | [last, ..earlier] => [{ last | trailing = Some comment }, ..earlier]
  | [] => []

--| An event after what is seen, as `placePiece` places its piece: a
--| blank line waits for the next token; a comment waits too if it starts
--| its line, and goes on the newest token otherwise; any other word is a
--| token of the kind its text spells, starting as the event says.
def viewEvent (seen: Views) (event: Event): Views :=
  if event.word == "\n" then { views = seen.views, pending = addBlank seen.pending }
  else
    match lexemeOf event.word with
      | CommentLexeme =>
        match event.start with
          | Some _ => { views = seen.views, pending = [OwnLine { text = event.word }, ..seen.pending] }
          | None => { views = viewTrailing seen.views { text = event.word }, pending = seen.pending }
      | lexeme => {
        views = [
          { kind = lexemeKind lexeme event.word, start = event.start, above = seen.pending.reverse, trailing = None },
          ..seen.views
        ],
        pending = []
      }

--| The views of a trace, in the order printed, after `seen`.
def viewsFrom (seen: Views) (events: List Event): Views := match events with
  | [] => seen
  | [event, ..rest] => viewsFrom (viewEvent seen event) rest

--| The token views a trace lexes to.
def viewsOf (events: List Event): Views := viewsFrom { views = [], pending = [] } events

theorem viewsSnoc ∀ (seen: Views) (events: List Event) (last: Event):
    viewsFrom seen (events ++ [last]) = viewEvent (viewsFrom seen events) last :=
  match events with
    | [] => byComputing
    | [event, ..rest] => viewsSnoc (viewEvent seen event) rest last

theorem trailingViews ∀ (tokens: List (Parse.Located Token)) (comment: Parse.Located Comment):
    (withTrailing tokens comment).map viewOf = viewTrailing (tokens.map viewOf) comment.value :=
  match tokens with
    | [] => byComputing
    | [last, ..earlier] => byComputing

theorem gapPlaced ∀ (piece: Text) (placed: Placed) (blank: Bool) (column offset: Nat)
    (gap: piece.all (char => char == ' ') = True):
    placePiece placed piece blank column offset = placed :=
  match spaces: piece.all (char => char == ' '), gap with
    | True, _ => byComputing
    | False, never =>
      match never with
        | ()

--| A word placed is its event seen.
theorem wordViews ∀ (piece: Text) (placed: Placed) (blank: Bool) (column offset: Nat)
    (oneLine: (piece == "\n") = False):
    (placeWord placed piece blank column offset).views
      = viewEvent placed.views { word = piece, start = if blank then Some column else None } :=
  match isBreak: piece == "\n", oneLine with
    | False, _ =>
      match lexeme: lexemeOf piece with
        | CommentLexeme =>
          match blank with
            | True => byComputing
            | False =>
              Eq.cong
                ((views: List TokenView) => ({ views, pending = placed.pending }: Views))
                (trailingViews placed.tokens { value = { text = piece }, offset, length = piece.length })
        | Spaces => byComputing
        | LineBreak => byComputing
        | WordLexeme => byComputing
        | DigitsLexeme => byComputing
        | StringLexeme => byComputing
        | SignLexeme => byComputing
        | SymbolsLexeme => byComputing
        | StrayLexeme => byComputing

theorem breakViews ∀ (earlier: List Text) (blank: Bool)
    (is: lineBlank earlier = blank)
    (rest: (placed earlier).views = viewsOf (eventsOf earlier)):
    (placed ["\n", ..earlier]).views = viewsOf (eventsOf ["\n", ..earlier]) :=
  match blank, is with
    | True, is =>
      Eq.trans
        (Eq.cong
          ((kept: Bool) =>
            ({
              views = (placed earlier).tokens.map viewOf,
              pending = if kept then addBlank (placed earlier).pending else (placed earlier).pending
            }: Views))
          is)
        (Eq.trans
          (Eq.cong ((seen: Views) => viewEvent seen Event.blankLine) rest)
          (Eq.flipped
            (Eq.trans
              (Eq.cong viewsOf (eventsBlank earlier is))
              (viewsSnoc { views = [], pending = [] } (eventsOf earlier) Event.blankLine))))
    | False, is =>
      Eq.trans
        (Eq.cong
          ((kept: Bool) =>
            ({
              views = (placed earlier).tokens.map viewOf,
              pending = if kept then addBlank (placed earlier).pending else (placed earlier).pending
            }: Views))
          is)
        (Eq.trans rest (Eq.flipped (Eq.cong viewsOf (eventsBreak earlier is))))

theorem pieceViews ∀ (piece: Text) (earlier: List Text) (spaces isBreak: Bool)
    (gap: piece.all (char => char == ' ') = spaces)
    (broken: (piece == "\n") = isBreak)
    (rest: (placed earlier).views = viewsOf (eventsOf earlier)):
    (placed [piece, ..earlier]).views = viewsOf (eventsOf [piece, ..earlier]) :=
  match spaces, isBreak, gap, broken with
    | True, _, gap, _ =>
      Eq.trans
        (Eq.cong Placed.views
          (gapPlaced piece (placed earlier) (lineBlank earlier) (lineWidth earlier) (charsLength earlier) gap))
        (Eq.trans rest (Eq.flipped (Eq.cong viewsOf (eventsGap piece earlier gap))))
    | False, True, _, broken =>
      let same: piece = "\n" := DecEq.sound broken
      rewrite same then breakViews earlier (lineBlank earlier) byComputing rest
    | False, False, gap, broken =>
      let word: isLayout piece = False := wordNotLayout piece gap broken
      let event: Event := { word = piece, start = if lineBlank earlier then Some (lineWidth earlier) else None }
      Eq.trans
        (Eq.cong Placed.views
          (wordPlaced piece (placed earlier) (lineBlank earlier) (lineWidth earlier) (charsLength earlier) word))
        (Eq.trans
          (wordViews piece (placed earlier) (lineBlank earlier) (lineWidth earlier) (charsLength earlier) broken)
          (Eq.trans
            (Eq.cong ((seen: Views) => viewEvent seen event) rest)
            (Eq.flipped
              (Eq.trans
                (Eq.cong viewsOf (eventsWord piece earlier word))
                (viewsSnoc { views = [], pending = [] } (eventsOf earlier) event)))))

--| The tokens of printed pieces, without their offsets, are the views of
--| the pieces' events: what the lexer makes of the text is a function of
--| the trace.
theorem placedViews ∀ (out: List Text): (placed out).views = viewsOf (eventsOf out) := match out with
  | [] => byComputing
  | [piece, ..earlier] => pieceViews piece earlier _ _ byComputing byComputing (placedViews earlier)

--| `viewsOf` computes: `f`, a blank line, then `x` at column 2 with a
--| comment after it.
theorem viewsExample: (viewsOf [
      { word = "f", start = Some 0 },
      Event.blankLine,
      { word = "x", start = Some 2 },
      { word = "-- c", start = None }
    ]).views
      = [
        { kind = Name "x", start = Some 2, above = [BlankLine], trailing = Some { text = "-- c" } },
        { kind = Name "f", start = Some 0, above = [], trailing = None }
      ] :=
  byComputing
