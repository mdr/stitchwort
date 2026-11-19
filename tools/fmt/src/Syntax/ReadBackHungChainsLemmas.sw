--| What the binary chains on any lines (`Syntax.ReadBackHungChains`) share: the line rule over an infix's parts, as
--| `infixParts` is for the one-line family. The operator and the right operand's first item stop no reading
--| (`hungStops`), the state after the operator enters the right operand as the left's first leaf did (`afterOperator`),
--| and the line rule and the bracket check split along the parts.

namespace Syntax.ReadBackHungChainsLemmas
import Std (Bool, List, Nat, Option, Void)
import Syntax (..)
import Fmt (..)
import Syntax.ReadBackProofs (..)
import Syntax.ReadBackRuns (..)
import Syntax.ReadBackLine (..)
import Syntax.ReadBackHung (..)
import Syntax.ReadBackHungBounds (..)
import Syntax.ReadBackHungFrame (..)
import Syntax.ReadBackHungFrameLemmas (..)

--| The line rule over two parts of leaves holds of the first from the state, and of the second from where the first
--| left it.
theorem hungSplit ∀ (state: HangState) (first rest: List Leaf)
    (hung: hangsFrom state (first ++ rest) = True):
    ∃ (mid: HangState) => state.after first = Some mid ∧ hangsFrom mid rest = True :=
  match first with
    | [] => (state, byComputing, hung)
    | [leaf, ..more] =>
      match stepped: state.step leaf with
        | Some next =>
          let (mid, done, held) := hungSplit next more rest hung
          (mid, done, held)

--| The line rule over a leaf and the leaves after it: the leaf's step, then the rest from its state.
theorem hungCons ∀ (state: HangState) (leaf: Leaf) (rest: List Leaf)
    (hung: hangsFrom state [leaf, ..rest] = True):
    ∃ (next: HangState) => state.step leaf = Some next ∧ hangsFrom next rest = True :=
  match stepped: state.step leaf with | Some next => (next, byComputing, hung)

--| A bracket check over two parts holds of the second.
theorem deepRight ∀ (first rest: List Item) (deep: deepAll (first ++ rest) = True): deepAll rest = True :=
  match first with
    | [] => deep
    | [item, ..more] => deepRight more rest (Bool.andRight deep)

--| A bracket check holds of a list's first item.
theorem deepHead ∀ (item: Item) (more: List Item) (deep: deepAll [item, ..more] = True): deepAll [item] = True :=
  rewrite Bool.andLeft deep

--| What an infix's parts tell, on any lines: `after` is the line rule's state after the operator, from where the
--| right operand is read.
type HungParts (modes: Modes) (state after: HangState) (leftRead: List Item) (op: Item) (rightRead tail: List
    Item): Prop = {
  lineLeft: lineAll leftRead = True,
  lineOpRight: lineAll [op, ..rightRead] = True,
  openLeft: openHead modes leftRead = True,
  boundLeft: bounds modes (state.enters leftRead) = True,
  openOp: modes.stops op = False,
  openRight: openHead modes rightRead = True,
  boundRight: bounds modes (after.enters rightRead) = True,
  hungRight: hangsFrom after (leavesOf (rightRead ++ tail)) = True,
  deepRight: deepAll (rightRead ++ tail) = True
}

--| What an infix's parts tell, from its items on any lines the line rule allows.
theorem hungParts ∀ (modes: Modes)
    (quiet: Quiet modes)
    (kind: InfixKind) (left right: Expr) (leftRead: List Item) (op: Item) (rightRead tail: List Item) (state: HangState)
    (leftSpelt: Spelt left leftRead)
    (rightSpelt: Spelt right rightRead)
    (isOp: infixTok kind op.kind = True)
    (lineRead: lineAll (leftRead ++ [op, ..rightRead]) = True)
    (openFirst: openHead modes (leftRead ++ [op, ..rightRead]) = True)
    (bound: bounds modes (state.enters (leftRead ++ [op, ..rightRead])) = True)
    (hung: hangsFrom state (leavesOf (leftRead ++ ([op, ..rightRead] ++ tail))) = True)
    (deepItems: deepAll (leftRead ++ ([op, ..rightRead] ++ tail)) = True):
    ∃ (after: HangState) => HungParts modes state after leftRead op rightRead tail :=
  let (f, fmore, isLeft, _) := speltStarts left leftRead leftSpelt
  let (r, rmore, isRight, rightLead) := speltStarts right rightRead rightSpelt
  let (lineLeft, lineOpRight) := lineSplit leftRead [op, ..rightRead] lineRead
  let boundF: bounds modes (state.entered f.leaf) = True := rewrite isLeft at bound then bound
  let openF: (!modes.stops f) = True := rewrite isLeft at openFirst then openFirst
  let (m1, leftAfter, hungRest) :=
    hungSplit state
      (leavesOf leftRead)
      (leavesOf ([op, ..rightRead] ++ tail))
      (rewrite leavesOfAppend leftRead ([op, ..rightRead] ++ tail) at hung then hung)
  let isM1: m1 = state.entered f.leaf := rewrite speltEnters left leftRead leftSpelt state m1 leftAfter, isLeft
  let (next, opStepped, hungNext) := hungCons m1 op.leaf (leavesOf (rightRead ++ tail)) hungRest
  let deepOp: deepAll [op, ..rightRead ++ tail] = True := deepRight leftRead _ deepItems
  let flat := infixIsFlat kind op.kind isOp
  let (notComma, notCloser, notColonEq, notColon, notOpener) := flatParts op.kind flat
  let boundM1: bounds modes m1 = True := rewrite isM1 then boundF
  let openOp: modes.stops op = False :=
    hungStops modes m1 next op quiet boundM1 opStepped (deepHead op _ deepOp) notColonEq
  let boundNext: bounds modes next = True :=
    boundsPast modes m1 next op
      (rewrite isM1, enteredTwice state f.leaf op.leaf then boundF)
      opStepped
      (rewrite notComma, notCloser, notColonEq, notColon)
  let closed := afterOperator state next f.leaf op.leaf r.leaf flat (rewrite isM1 at opStepped then opStepped)
  let boundRight: bounds modes (next.enters rightRead) = True := rewrite isRight, closed then boundF
  let (rest1, rightStepped, _) :=
    hungCons next r.leaf (leavesOf (rmore ++ tail)) (rewrite isRight at hungNext then hungNext)
  let deepRightItems: deepAll (rightRead ++ tail) = True := deepRight [op] _ deepOp
  let (notCloserR, notCommaR, notColonEqR) := leadNotBracket r.kind rightLead
  let openRightFirst: modes.stops r = False :=
    hungStops modes next rest1 r quiet boundNext rightStepped
      (deepHead r (rmore ++ tail) (rewrite isRight at deepRightItems then deepRightItems))
      notColonEqR
  (
    next,
    {
      lineLeft,
      lineOpRight,
      openLeft = rewrite isLeft then openHeadOf modes f fmore (notTrueFalse _ openF),
      boundLeft = rewrite isLeft then boundF,
      openOp,
      openRight = rewrite isRight then openHeadOf modes r rmore openRightFirst,
      boundRight,
      hungRight = hungNext,
      deepRight = deepRightItems
    }
  )
