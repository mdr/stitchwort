--| `&&`, `||`, `->` and the inline expression on any lines (H8 of SW-4121's plan): `logicLinks`, `logicAfterLinks`,
--| `logicOperator`, `operatorLine`, `arrowLine`, `inlinePlainLine` and `inlineLine` with the line rule's state in
--| place of "starts no line", as in `Syntax.ReadBackHungAtoms`. The arrow is where the line rule's `glue` is used: the
--| leaf after `->` starts no line, so its right side opens no block.

namespace Syntax.ReadBackHungInline
import Std (Bool, List, Nat, Option, Parse)
import Syntax (..)
import Fmt (..)
import Syntax.ReadBackProofs (..)
import Syntax.ReadBackRuns (..)
import Syntax.ReadBackTree (..)
import Syntax.ReadBackEnds (..)
import Syntax.ReadBackLine (..)
import Syntax.ReadBackHung (..)
import Syntax.ReadBackHungChains (..)

--| `cmpHung` at `depth` in `modes`, as a hypothesis: the logic chain's lemmas take it, as the one-line family's take
--| `CmpLineAt`.
def CmpHungAt (modes: Modes) (depth: Nat): Prop :=
  ∀ (expr: Expr) (read rest: List Item) (state: HangState) => expr.nest1 <= depth
    → Spelt expr read
    → expr.autoFree1 = True
    → lineAll read = True
    → lineAll rest = True
    → openHead modes read = True
    → bounds modes (state.enters read) = True
    → hangsFrom state (leavesOf (read ++ rest)) = True
    → deepAll (read ++ rest) = True
    → EndsAt modes 6 rest
    → 6 <= expr.level
    → CmpReads (TreeN depth) modes read rest expr

--| A logic chain's links, each `&&` or `||` and its comparison: `state` is the line rule's before the first link.
theorem logicLinksHung ∀ (modes: Modes)
    (quiet: Quiet modes) (depth: Nat)
    (cmp: CmpHungAt modes depth)
    (links: List (Item, List Item, Expr)) (rest: List Item) (state: HangState)
    (linksSpelt: LinksSpelt depth links)
    (lineLinks: lineAll (Parse.loopReads [] (linkSteps links)) = True)
    (lineRest: lineAll rest = True)
    (bound: bounds modes state = True)
    (hung: hangsFrom state (leavesOf (Parse.loopReads [] (linkSteps links) ++ rest)) = True)
    (deepItems: deepAll (Parse.loopReads [] (linkSteps links) ++ rest) = True)
    (ends: EndsAt modes 5 rest):
    LogicReads (TreeN depth) modes links rest :=
  ?

--| After a logic chain's links, regrouped.
theorem logicAfterLinksHung ∀ (modes: Modes)
    (quiet: Quiet modes)
    (depth: Nat) (links: List (Item, List Item, Expr)) (rest: List Item) (first expr: Expr) (state: HangState)
    (linksSpelt: LinksSpelt depth links)
    (group: groupLogic (Succ links.length) first (Parse.stepValues (linkSteps links)) = expr)
    (bound: bounds modes state = True)
    (hung: hangsFrom state (leavesOf (Parse.loopReads [] (linkSteps links) ++ rest)) = True)
    (deepItems: deepAll (Parse.loopReads [] (linkSteps links) ++ rest) = True)
    (noAndOr: andOrOn modes rest = False)
    (logic: LogicReads (TreeN depth) modes links rest):
    LogicAfterReads (TreeN depth) modes first (Parse.loopReads [] (linkSteps links)) rest expr :=
  ?

--| An operator expression whose lowest operator is `&&` or `||`.
theorem logicOperatorHung ∀ (modes: Modes)
    (quiet: Quiet modes)
    (expr: Expr) (read read3 rest: List Item) (depth: Nat) (all: List Item) (value: Expr) (state: HangState)
    (cmp: CmpHungAt modes depth)
    (whole: all = read ++ read3)
    (deep: expr.nest1 <= depth)
    (spelt: Spelt expr read)
    (free: expr.autoFree1 = True)
    (lineRead: lineAll read = True)
    (lineAfter: lineAll (read3 ++ rest) = True)
    (openFirst: openHead modes read = True)
    (bound: bounds modes (state.enters read) = True)
    (hung: hangsFrom state (leavesOf (read ++ (read3 ++ rest))) = True)
    (deepItems: deepAll (read ++ (read3 ++ rest)) = True)
    (ends: EndsAt modes 5 (read3 ++ rest))
    (low: 4 <= expr.level)
    (noSection: isSome Dot (peekIn modes 0 ((read ++ read3) ++ rest)) = False)
    (ending: EndReads (TreeN depth) modes expr (sequenceOn modes (read3 ++ rest)) read3 rest value):
    OperatorReads (TreeN depth) modes all rest value :=
  ?

--| What `operator` reads: the expression up to an arrow or the end, then what ends it.
theorem operatorHung ∀ (modes: Modes)
    (quiet: Quiet modes)
    (expr: Expr) (read read3 rest: List Item) (depth: Nat) (all: List Item) (value: Expr) (state: HangState)
    (inner: FullHungBelow depth)
    (whole: all = read ++ read3)
    (deep: expr.nest1 <= depth)
    (spelt: Spelt expr read)
    (free: expr.autoFree1 = True)
    (lineRead: lineAll read = True)
    (lineAfter: lineAll (read3 ++ rest) = True)
    (openFirst: openHead modes read = True)
    (bound: bounds modes (state.enters read) = True)
    (hung: hangsFrom state (leavesOf (read ++ (read3 ++ rest))) = True)
    (deepItems: deepAll (read ++ (read3 ++ rest)) = True)
    (ends: EndsAt modes 5 (read3 ++ rest))
    (fits: 2 <= expr.level)
    (noSection: isSome Dot (peekIn modes 0 ((read ++ read3) ++ rest)) = False)
    (ending: EndReads (TreeN depth) modes expr (sequenceOn modes (read3 ++ rest)) read3 rest value):
    OperatorReads (TreeN depth) modes all rest value :=
  ?

--| An arrow, its right side read in full one level down: the leaf after `->` starts no line (the line rule's
--| `glue`).
theorem arrowHung ∀ (modes: Modes)
    (quiet: Quiet modes)
    (left right: Expr) (operator: Word) (item: Item) (more rest: List Item) (depth: Nat) (state: HangState)
    (inner: FullHungBelow depth)
    (deep: (Infix InfixArrow left operator right).nest1 <= depth)
    (spelt: Spelt (Infix InfixArrow left operator right) [item, ..more])
    (free: (Infix InfixArrow left operator right).autoFree1 = True)
    (lineRead: lineAll [item, ..more] = True)
    (lineRest: lineAll rest = True)
    (open: modes.stops item = False)
    (bound: bounds modes (state.entered item.leaf) = True)
    (hung: hangsFrom state (leavesOf ([item, ..more] ++ rest)) = True)
    (deepItems: deepAll ([item, ..more] ++ rest) = True)
    (ends: endsHere rest = True):
    InlineAt (TreeN depth) modes item more rest (Infix InfixArrow left operator right) :=
  ?

--| An inline expression with no arrow at its top.
theorem inlinePlainHung ∀ (modes: Modes)
    (quiet: Quiet modes)
    (expr: Expr) (item: Item) (more rest: List Item) (depth: Nat) (state: HangState)
    (inner: FullHungBelow depth)
    (deep: expr.nest1 <= depth)
    (spelt: Spelt expr [item, ..more])
    (free: expr.autoFree1 = True)
    (lineRead: lineAll [item, ..more] = True)
    (lineRest: lineAll rest = True)
    (open: modes.stops item = False)
    (bound: bounds modes (state.entered item.leaf) = True)
    (hung: hangsFrom state (leavesOf ([item, ..more] ++ rest)) = True)
    (deepItems: deepAll ([item, ..more] ++ rest) = True)
    (ends: endsHere rest = True)
    (fits: 2 <= expr.level):
    InlineAt (TreeN depth) modes item more rest expr :=
  ?

--| The rungs below `expr` (`inlineLine`, `operatorLine`, the chains, `unaryLine`, `appLine`, `atomLine`): today's
--| statement with `inLater` and `restOpen` replaced by the state before the first item, the bound against the state
--| that item enters, and the line rule over the items and what follows. `open` stays: the first item is the caller's
--| to place (a block's own first item is allowed by its modes, not by its column).
theorem inlineHung ∀ (modes: Modes)
    (quiet: Quiet modes)
    (expr: Expr) (item: Item) (more rest: List Item) (depth: Nat) (state: HangState)
    (inner: FullHungBelow depth)
    (deep: expr.nest1 <= depth)
    (spelt: Spelt expr [item, ..more])
    (free: expr.autoFree1 = True)
    (lineRead: lineAll [item, ..more] = True)
    (lineRest: lineAll rest = True)
    (open: modes.stops item = False)
    (bound: bounds modes (state.entered item.leaf) = True)
    (hung: hangsFrom state (leavesOf ([item, ..more] ++ rest)) = True)
    (deepItems: deepAll ([item, ..more] ++ rest) = True)
    (ends: endsHere rest = True):
    InlineAt (TreeN depth) modes item more rest expr :=
  ?
