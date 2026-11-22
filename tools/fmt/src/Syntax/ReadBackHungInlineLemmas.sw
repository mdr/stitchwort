--| The line rule's state through a logic chain and an arrow, for H8 of SW-4121's plan: an operator that is no
--| bracket, comma or `:` stops no reading the state bounds, the state after a spelt expression keeps the rule over what
--| follows, the links' operators end their comparisons, and `->` leaves the state glued with its column in force.

namespace Syntax.ReadBackHungInlineLemmas
import Std (Bool, DecEq, Eq, List, Nat, Option, Parse)
import Syntax (..)
import Fmt (..)
import Syntax.ReadBackProofs (..)
import Syntax.ReadBackRuns (..)
import Syntax.ReadBackTree (..)
import Syntax.ReadBackLine (..)
import Syntax.ReadBackHung (..)
import Syntax.ReadBackHungBounds (..)
import Syntax.ReadBackHungFrame (speltEnters)
import Syntax.ReadBackHungFrameLemmas (leavesOfAppend, idleArrow, infixIsFlat, flatParts)
import Syntax.ReadBackHungAtomsLemmas (..)

--| `&&` and `||` are no comma, closer, `:=` or `:`.
theorem andOrPlain ∀ (kind: Tok)
    (andOr: (kind == AndAnd || kind == OrOr) = True):
    (kind == Comma || kind.isCloser || kind == ColonEq || kind == Colon) = False :=
  cases

--| An item that is no comma, closer, `:=` or `:` doesn't stop a reading the state bounds, and leaves a state the
--| bound holds of.
theorem plainHung ∀ (modes: Modes) (state: HangState) (item: Item) (rest: List Item)
    (quiet: QuietModes modes)
    (plain: (item.kind == Comma || item.kind.isCloser || item.kind == ColonEq || item.kind == Colon) = False)
    (bound: bounds modes state = True)
    (hung: hangsFrom state (leavesOf [item, ..rest]) = True):
    modes.stops item = False
      ∧ ∃ (next: HangState) => bounds modes next = True ∧ hangsFrom next (leavesOf rest) = True :=
  let (next, stepped, hungRest) := hungStep state item.leaf (leavesOf rest) hung
  let (notComma, others) := Bool.orFalseElim _ _ plain
  let (notCloser, others2) := Bool.orFalseElim _ _ others
  let (notAssign, _) := Bool.orFalseElim _ _ others2
  let entered := boundsEntered modes state next item.leaf bound stepped plain
  (
    hungStops modes state next item quiet bound stepped (deepOf item notComma notCloser) notAssign,
    (next, boundsPast modes state next item entered stepped plain, hungRest)
  )

--| After a spelt expression, the line rule goes on from the state its first leaf entered.
theorem speltAfterHung ∀ (expr: Expr) (read rest: List Item) (state: HangState)
    (spelt: Spelt expr read)
    (hung: hangsFrom state (leavesOf (read ++ rest)) = True):
    hangsFrom (state.enters read) (leavesOf rest) = True :=
  let (mid, after, hungRest) :=
    hungSplit state (leavesOf read) (leavesOf rest) (rewrite <- leavesOfAppend read rest then hung)
  rewrite <- speltEnters expr read spelt state mid after then hungRest

--| What follows a comparison in a logic chain on any lines ends it there: the next link's `&&` or `||`, or what ends
--| the chain. `linksEnds` with the line rule's state before the links in place of "starts no line".
theorem linksEndsHung ∀ (modes: Modes)
    (quiet: QuietModes modes)
    (depth: Nat) (links: List (Item, List Item, Expr)) (rest: List Item) (state: HangState)
    (linksSpelt: LinksSpelt depth links)
    (bound: bounds modes state = True)
    (hung: hangsFrom state (leavesOf (Parse.loopReads [] (linkSteps links) ++ rest)) = True)
    (ends: EndsAt modes 5 rest):
    EndsAt modes 6 (Parse.loopReads [] (linkSteps links) ++ rest) :=
  match links, linksSpelt with
    | [], _ => endsAtUp modes 5 6 rest (arithmetic []) ends
    | [(op, read, value), ..later], (andOr, apart, operand, _) =>
      let after := Parse.loopReads [] (linkSteps later)
      let (open, _) := plainHung modes state op ((read ++ after) ++ rest) quiet (andOrPlain op.kind andOr) bound hung
      rewrite List.appendAssoc read after rest then
        opEnds modes 6 op
          (read ++ (after ++ rest))
          InfixBinary
          open
          (andOrBinary op.kind andOr)
          (rewrite speltApart value read (after ++ rest) operand.spelt then apart)
          (rewrite andOrRung op.kind andOr then arithmetic [])

--| `->` after a spelt left side on any lines: it stops no reading the state the left side's first leaf entered
--| bounds, and leaves the state glued, with the same column in force, from which the rule goes on over the right side
--| and what follows.
theorem arrowHungParts ∀ (modes: Modes)
    (quiet: QuietModes modes)
    (left: Expr) (leftRead: List Item) (arrow: Item) (rightRead rest: List Item) (state: HangState)
    (leftSpelt: Spelt left leftRead)
    (isOp: infixTok InfixArrow arrow.kind = True)
    (bound: bounds modes (state.enters leftRead) = True)
    (hung: hangsFrom state (leavesOf (leftRead ++ ([arrow, ..rightRead] ++ rest))) = True):
    modes.stops arrow = False
      ∧ ∃ (next: HangState) => next.glue = True
        ∧ bounds modes next = True
        ∧ hangsFrom next (leavesOf (rightRead ++ rest)) = True :=
  let hungArrow := speltAfterHung left leftRead ([arrow, ..rightRead] ++ rest) state leftSpelt hung
  let (next, stepped, hungRight) := hungStep (state.enters leftRead) arrow.leaf (leavesOf (rightRead ++ rest)) hungArrow
  let flat := infixIsFlat InfixArrow arrow.kind isOp
  let (notComma, notCloser, _) := flatParts arrow.kind flat
  let (first, inside, isLeft, _) := speltStarts left leftRead leftSpelt
  let idle: (state.enters leftRead).start = False := rewrite isLeft
  let isNext := idleArrow (state.enters leftRead) next arrow.leaf idle flat isOp stepped
  (
    hungStops modes
      (state.enters leftRead)
      next
      arrow
      quiet
      bound
      stepped
      (deepOf arrow notComma notCloser)
      (exprNotColonEq arrow.kind (infixExpr InfixArrow arrow.kind isOp)),
    (next, (rewrite isNext), boundsCong modes next (state.enters leftRead) (rewrite isNext) bound, hungRight)
  )
