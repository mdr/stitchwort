--| Events as the parser needs them inside brackets, where it asks
--| nothing of where a token starts its line: whatever events the rules
--| lay for an expression in any zone are its events in the zone of
--| brackets around a statement at column 0 (`eventsFree`), where every
--| start is allowed, and a body of one expression, on its keyword's line
--| or below it, is that expression's events there (`bodyFree`).

namespace Toy.Fmt.Proofs
import Toy.Doc (..)
import Toy.Doc.Proofs (..)
import Toy.Syntax (..)
import Toy.Syntax.Proofs (..)
import Toy.Fmt (..)
import Std (Bool, DecEq, Eq, List, Nat, Option, Parse, Text, Void)

--| A token that starts as `strong` allows starts as anything weaker does.
theorem tokenWider ∀ (strong weak: Option Nat → Prop) (comments: Comments) (text: Text)
    (events: List Event) (wider: ∀ (start: Option Nat) => strong start → weak start)
    (holds: TokenAt strong comments text events):
    TokenAt weak comments text events :=
  match holds with
    | Witness column (Witness start (Both allowed same)) =>
      Witness column (Witness start (Both (wider start allowed) same))

theorem thenWider ∀ (first second widerFirst widerSecond: List Event → Prop) (events: List Event)
    (one: ∀ (part: List Event) => first part → widerFirst part)
    (other: ∀ (part: List Event) => second part → widerSecond part)
    (holds: Then first second events):
    Then widerFirst widerSecond events :=
  match holds with
    | Witness front (Witness back (Both split (Both isFirst isSecond))) =>
      Witness front (Witness back (Both split (Both (one front isFirst) (other back isSecond))))

theorem freeAllows ∀ (start: Option Nat): (Anywhere 0).allows start := rfl

theorem freeReaches ∀ (start: Option Nat): (Anywhere 0).reaches start := match start with
  | None => rfl
  | Some at => omega

--| An expression's events in any zone, its leftmost token starting as
--| `head` says, are its events inside brackets with that token starting
--| as anything weaker says.
theorem eventsFree ∀ (zone: Zone) (head wide: Option Nat → Prop) (expr: Expr)
    (events: List Event) (wider: ∀ (start: Option Nat) => head start → wide start)
    (holds: Events zone head expr events):
    Events (Anywhere 0) wide expr events :=
  match expr, holds with
    | Var name comments, holds => tokenWider head wide comments name events wider holds
    | NumberLiteral digits comments, holds => tokenWider head wide comments digits events wider holds
    | StringLiteral written comments, holds => tokenWider head wide comments written events wider holds
    | Bracketed open inner close, holds =>
      thenWider _ _ _ _ events
        (part held => tokenWider head wide open "(" part wider held)
        (part held =>
          thenWider _ _ _ _ part
            (piece laid => eventsFree zone.inside anyStart anyStart inner piece (start any => any) laid)
            (piece laid => laid)
            held)
        holds
    | ListLiteral open items close, holds =>
      thenWider _ _ _ _ events
        (part held => tokenWider head wide open "[" part wider held)
        (part held =>
          thenWider _ _ _ _ part (piece laid => itemsFree zone.inside items piece laid) (piece laid => laid) held)
        holds
    | Call callee open arguments close, holds =>
      thenWider _ _ _ _ events
        (part held => eventsFree zone head wide callee part wider held)
        (part held =>
          thenWider _ _ _ _ part
            (piece laid =>
              tokenWider zone.allows (Anywhere 0).allows open "(" piece (start any => freeAllows start) laid)
            (piece laid =>
              thenWider _ _ _ _ piece
                (last found => itemsFree zone.inside arguments last found)
                (last found => found)
                laid)
            held)
        holds
    | Field target dot name nameComments, holds =>
      thenWider _ _ _ _ events
        (part held => eventsFree zone head wide target part wider held)
        (part held =>
          thenWider _ _ _ _ part
            (piece laid =>
              tokenWider zone.allows (Anywhere 0).allows dot "." piece (start any => freeAllows start) laid)
            (piece laid =>
              tokenWider zone.allows (Anywhere 0).allows nameComments name piece (start any => freeAllows start) laid)
            held)
        holds
    | Negate minus operand, holds =>
      thenWider _ _ _ _ events
        (part held => tokenWider head wide minus "-" part wider held)
        (part held => eventsFree zone zone.allows (Anywhere 0).allows operand part (start any => freeAllows start) held)
        holds
    | Binary operator sign left right, holds =>
      thenWider _ _ _ _ events
        (part held => eventsFree zone head wide left part wider held)
        (part held =>
          thenWider _ _ _ _ part
            (piece laid =>
              tokenWider zone.allows
                (Anywhere 0).allows
                sign
                operator.spelling
                piece
                (start any => freeAllows start)
                laid)
            (piece laid =>
              eventsFree zone zone.allows (Anywhere 0).allows right piece (start any => freeAllows start) laid)
            held)
        holds
    | If ifComments condition thenComments whenTrue elseComments whenFalse, holds =>
      thenWider _ _ _ _ events
        (part held => tokenWider head wide ifComments "if" part wider held)
        (part held =>
          thenWider _ _ _ _ part
            (piece laid =>
              eventsFree zone zone.allows (Anywhere 0).allows condition piece (start any => freeAllows start) laid)
            (piece laid =>
              thenWider _ _ _ _ piece
                (last found =>
                  tokenWider zone.allows
                    (Anywhere 0).allows
                    thenComments
                    "then"
                    last
                    (start any => freeAllows start)
                    found)
                (last found =>
                  thenWider _ _ _ _ last
                    (tail kept => bodyEventsFree zone whenTrue tail kept)
                    (tail kept =>
                      thenWider _ _ _ _ tail
                        (end met =>
                          tokenWider zone.reaches
                            (Anywhere 0).reaches
                            elseComments
                            "else"
                            end
                            (start any => freeReaches start)
                            met)
                        (end met => bodyEventsFree zone whenFalse end met)
                        kept)
                    found)
                laid)
            held)
        holds

theorem itemsFree ∀ (zone: Zone) (items: List Item) (events: List Event)
    (holds: ItemEvents zone items events):
    ItemEvents (Anywhere 0) items events :=
  match items, holds with
    | [], holds => holds
    | [{ value, comma }], holds => eventsFree zone anyStart anyStart value events (start any => any) holds
    | [{ value, comma }, second, ..rest], holds =>
      thenWider _ _ _ _ events
        (part held => eventsFree zone anyStart anyStart value part (start any => any) held)
        (part held =>
          thenWider _ _ _ _ part (piece laid => laid) (piece laid => itemsFree zone [second, ..rest] piece laid) held)
        holds

--| A body's events in any zone are its events inside brackets: on its
--| keyword's line with nothing asked of its first token's start but
--| what its comments say, or as lines at a column.
theorem bodyEventsFree ∀ (zone: Zone) (body: Body) (events: List Event)
    (holds: BodyEvents zone body events):
    BodyEvents (Anywhere 0) body events :=
  match body, holds with
    | { statements = [{ blankBefore, line = Bare value }] }, Inl inline =>
      Inl
        (eventsFree zone
          (inlineHead zone value)
          (inlineHead (Anywhere 0) value)
          value
          events
          (start allowed =>
            match allowed with
              | Both _ plain => Both (freeAllows start) plain)
          inline)
    | { statements }, Inr (Witness column (Both under lines)) => Inr (Witness column (Both (omega) lines))

--| Inside brackets the parser reads a body as one expression, wherever
--| its tokens start: a body of one expression, laid on its keyword's
--| line or on a line of its own below, is that expression's events with
--| nothing asked of its first token's start.
theorem bodyFree ∀ (zone: Zone) (blankBefore: Bool) (value: Expr) (events: List Event)
    (holds: BodyEvents zone { statements = [{ blankBefore, line = Bare value }] } events):
    Events (Anywhere 0) anyStart value events :=
  match holds with
    | Inl inline => eventsFree zone (inlineHead zone value) anyStart value events (start allowed => rfl) inline
    | Inr (Witness column (Both under (Witness front (Witness back (Both split (Both isValue done)))))) =>
      let whole: events = front := rewrite split, done in List.appendNil front
      rewrite whole in eventsFree (Deeper column) (atColumn column) anyStart value front (start allowed => rfl) isValue
