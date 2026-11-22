--| What the binary chains on any lines (`Syntax.ReadBackHungChains`) share: the line rule over an infix's parts
--| (`HungParts`). The operator and the right operand's first item stop no reading
--| (`hungStops`), the state after the operator enters the right operand as the left's first leaf did (`afterOperator`),
--| and the line rule and the bracket check split along the parts.

namespace Syntax.ReadBackHungChainsLemmas
import Std (Bool, List, Nat, Option, Parse, Void)
import Syntax (..)
import Fmt (..)
import Syntax.ReadBackProofs (..)
import Syntax.ReadBackRuns (..)
import Syntax.ReadBackLine (..)
import Syntax.ReadBackHung (..)
import Syntax.ReadBackHungBounds (..)
import Syntax.ReadBackHungFrame (..)
import Syntax.ReadBackHungFrameLemmas (..)
import Syntax.ReadBackHungAtomsLemmas (deepHead, deepRest, hungSplit, hungStep)

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
    (quiet: QuietModes modes)
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
  let (next, opStepped, hungNext) := hungStep m1 op.leaf (leavesOf (rightRead ++ tail)) hungRest
  let deepOp: deepAll [op, ..rightRead ++ tail] = True := deepRest leftRead _ deepItems
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
    hungStep next r.leaf (leavesOf (rmore ++ tail)) (rewrite isRight at hungNext then hungNext)
  let deepRightItems: deepAll (rightRead ++ tail) = True := deepRest [op] _ deepOp
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
      openLeft = rewrite isLeft then openHeadOf modes f fmore (Bool.notTrue _ openF),
      boundLeft = rewrite isLeft then boundF,
      openOp,
      openRight = rewrite isRight then openHeadOf modes r rmore openRightFirst,
      boundRight,
      hungRight = hungNext,
      deepRight = deepRightItems
    }
  )

--| Uses an `∃` without a `match`: a destructuring `let` over a witness generalises like a `match` and re-reads every
--| hypothesis in scope, while a call that takes the continuation doesn't.
theorem withWitness ∀ (p: a → Prop) (found: ∃ (x: a) => p x) (goal: Prop) (use: ∀ (x: a) => p x → goal): goal :=
  match found with | Witness x holds => use x holds

--| What one link of a chain adds to the line rule's facts, from the first operand `leftRead` taking `[op, ..rightRead]`
--| off the front of the links' reads: the infix's parts, the line rule over the shorter chain's reads and the facts
--| the first operand is left with.
type ChainStep (modes: Modes) (state after: HangState) (leftRead: List Item) (op: Item) (rightRead: List
    Item) (right: Expr) (links: List (Item, List Item, Expr)) (rest: List Item): Prop = {
  parts: HungParts modes state after leftRead op rightRead (Parse.loopReads [] (linkSteps links) ++ rest),
  lineTail: lineAll (Parse.loopReads [] (linkSteps [(op, rightRead, right), ..links]) ++ rest) = True,
  hungTail: hangsFrom state
    (leavesOf (leftRead ++ (Parse.loopReads [] (linkSteps [(op, rightRead, right), ..links]) ++ rest)))
    = True,
  deepTail: deepAll (leftRead ++ (Parse.loopReads [] (linkSteps [(op, rightRead, right), ..links]) ++ rest)) = True
}

--| `hungParts` over an infix whose operands read `leftRead` and `rightRead` ahead of a chain's other links: the facts the
--| recursion needs about the left operand and the shorter chain's reads, taken from the whole chain's facts. A lemma of
--| its own so the rewrites in it don't read back the large hypotheses of the chain proofs.
theorem chainStep ∀ (modes: Modes)
    (quiet: QuietModes modes)
    (kind: InfixKind) (left right: Expr) (read leftRead: List Item) (op: Item) (rightRead: List Item)
    (links: List (Item, List Item, Expr)) (rest: List Item) (state: HangState)
    (leftSpelt: Spelt left leftRead)
    (rightSpelt: Spelt right rightRead)
    (isOp: infixTok kind op.kind = True)
    (isRead: read = leftRead ++ [op, ..rightRead])
    (facts: HungAt modes state read (Parse.loopReads [] (linkSteps links) ++ rest)):
    ∃ (after: HangState) => ChainStep modes state after leftRead op rightRead right links rest :=
  let rightAfter := Parse.loopReads [] (linkSteps links) ++ rest
  let hungL: hangsFrom state (leavesOf (leftRead ++ ([op, ..rightRead] ++ rightAfter))) = True :=
    rewrite <- List.appendAssoc leftRead [op, ..rightRead] rightAfter, <- isRead then facts.hung
  let deepL: deepAll (leftRead ++ ([op, ..rightRead] ++ rightAfter)) = True :=
    rewrite <- List.appendAssoc leftRead [op, ..rightRead] rightAfter, <- isRead then facts.deepItems
  withWitness _
    (hungParts modes quiet kind left right leftRead op rightRead rightAfter state leftSpelt rightSpelt isOp
      (rewrite <- isRead then facts.lineRead)
      (rewrite <- isRead then facts.openFirst)
      (rewrite <- isRead then facts.bound)
      hungL
      deepL) _
    (after parts =>
      Witness after {
        parts = parts,
        lineTail = rewrite List.appendAssoc rightRead (Parse.loopReads [] (linkSteps links)) rest then
          lineJoin [op, ..rightRead] rightAfter parts.lineOpRight facts.lineRest,
        hungTail = (rewrite List.appendAssoc rightRead (Parse.loopReads [] (linkSteps links)) rest then hungL),
        deepTail = (rewrite List.appendAssoc rightRead (Parse.loopReads [] (linkSteps links)) rest then deepL)
      })

--| The chain's reads, and its value, after one link moves from the first operand to the links.
theorem chainWhole ∀ (all read leftRead: List Item) (op: Item) (rightRead: List Item)
    (links: List (Item, List Item, Expr)) (right: Expr)
    (whole: all = read ++ Parse.loopReads [] (linkSteps links))
    (isRead: read = leftRead ++ [op, ..rightRead]):
    all = leftRead ++ Parse.loopReads [] (linkSteps [(op, rightRead, right), ..links]) :=
  rewrite whole, isRead then List.appendAssoc leftRead [op, ..rightRead] (Parse.loopReads [] (linkSteps links))

theorem chainValue ∀ (value left right: Expr) (operator: Word) (op: Item)
    (rightRead: List Item) (links: List (Item, List Item, Expr))
    (isValue: value = leftNested (Infix InfixBinary left operator right) (Parse.stepValues (linkSteps links)))
    (isWord: op.leaf.word = operator):
    value = leftNested left (Parse.stepValues (linkSteps [(op, rightRead, right), ..links])) :=
  rewrite isValue, isWord

--| A fact about the reads of the links after `rightRead`, moved to the links with that operand taken off the first
--| operand.
theorem chainReads ∀ (facts: List Item → Prop)
    (rightRead later rest: List Item) (holds: facts (rightRead ++ (later ++ rest))):
    facts ((rightRead ++ later) ++ rest) :=
  rewrite List.appendAssoc rightRead later rest then holds
