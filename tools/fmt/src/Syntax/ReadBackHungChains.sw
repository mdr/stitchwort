--| The binary chains on any lines (H7 of SW-4121's plan): `mulAcc`, `mulLine`, `addAcc`, `addBase`, `addLine`,
--| `appendLine`, `appendBase`, `cmpAlone` and `cmpLine` with the line rule's state in place of "starts no line",
--| as in `Syntax.ReadBackHungAtoms`. The accumulators' line rule runs over the operand and the links after it.

namespace Syntax.ReadBackHungChains
import Std (Bool, List, Nat, Option, Parse)
import Syntax (..)
import Fmt (..)
import Syntax.ReadBackProofs (..)
import Syntax.ReadBackRuns (..)
import Syntax.ReadBackTree (..)
import Syntax.ReadBackEnds (..)
import Syntax.ReadBackLine (..)
import Syntax.ReadBackHung (..)
import Syntax.ReadBackHungApp (..)

--| `* / %` links after a first operand, nested to the left.
theorem mulAccHung ∀ (modes: Modes)
    (quiet: Quiet modes)
    (expr: Expr) (read: List Item) (links: List (Item, List Item, Expr)) (rest: List Item) (depth: Nat) (all: List Item)
    (value: Expr) (state: HangState)
    (inner: FullHungBelow depth)
    (whole: all = read ++ Parse.loopReads [] (linkSteps links))
    (isValue: value = leftNested expr (Parse.stepValues (linkSteps links)))
    (deep: expr.nest1 <= depth)
    (spelt: Spelt expr read)
    (free: expr.autoFree1 = True)
    (lineRead: lineAll read = True)
    (lineAfter: lineAll (Parse.loopReads [] (linkSteps links) ++ rest) = True)
    (openFirst: openHead modes read = True)
    (bound: bounds modes (state.enters read) = True)
    (hung: hangsFrom state (leavesOf (read ++ (Parse.loopReads [] (linkSteps links) ++ rest))) = True)
    (deepItems: deepAll (read ++ (Parse.loopReads [] (linkSteps links) ++ rest)) = True)
    (after: UnaryEnds modes (Parse.loopReads [] (linkSteps links) ++ rest))
    (linked: LinkReads modes
      (kind => kind == Star || kind == Slash || kind == Percent)
      (UnaryReads (TreeN depth) modes)
      links
      rest)
    (fits: 16 <= expr.level):
    MulReads (TreeN depth) modes all rest value :=
  ?

--| The `* / %` level.
theorem mulHung ∀ (modes: Modes)
    (quiet: Quiet modes)
    (expr: Expr) (read rest: List Item) (depth: Nat) (state: HangState)
    (inner: FullHungBelow depth)
    (deep: expr.nest1 <= depth)
    (spelt: Spelt expr read)
    (free: expr.autoFree1 = True)
    (lineRead: lineAll read = True)
    (lineRest: lineAll rest = True)
    (openFirst: openHead modes read = True)
    (bound: bounds modes (state.enters read) = True)
    (hung: hangsFrom state (leavesOf (read ++ rest)) = True)
    (deepItems: deepAll (read ++ rest) = True)
    (ends: EndsAt modes 16 rest)
    (fits: 16 <= expr.level):
    MulReads (TreeN depth) modes read rest expr :=
  ?

--| `+ -` links after a first operand of the `+` level, nested to the left.
theorem addAccHung ∀ (modes: Modes)
    (quiet: Quiet modes)
    (expr: Expr) (read: List Item) (links: List (Item, List Item, Expr)) (rest: List Item) (depth: Nat) (all: List Item)
    (value: Expr) (state: HangState)
    (inner: FullHungBelow depth)
    (whole: all = read ++ Parse.loopReads [] (linkSteps links))
    (isValue: value = leftNested expr (Parse.stepValues (linkSteps links)))
    (deep: expr.nest1 <= depth)
    (spelt: Spelt expr read)
    (free: expr.autoFree1 = True)
    (lineRead: lineAll read = True)
    (lineAfter: lineAll (Parse.loopReads [] (linkSteps links) ++ rest) = True)
    (openFirst: openHead modes read = True)
    (bound: bounds modes (state.enters read) = True)
    (hung: hangsFrom state (leavesOf (read ++ (Parse.loopReads [] (linkSteps links) ++ rest))) = True)
    (deepItems: deepAll (read ++ (Parse.loopReads [] (linkSteps links) ++ rest)) = True)
    (after: EndsAt modes 16 (Parse.loopReads [] (linkSteps links) ++ rest))
    (linked: LinkReads modes (kind => kind == Plus || kind == Minus) (MulReads (TreeN depth) modes) links rest)
    (fits: 14 <= expr.level):
    AddReads (TreeN depth) modes all rest value :=
  ?

--| `+ -` links after a first operand above the `+` level.
theorem addBaseHung ∀ (modes: Modes)
    (quiet: Quiet modes)
    (expr: Expr) (read: List Item) (links: List (Item, List Item, Expr)) (rest: List Item) (depth: Nat) (all: List Item)
    (value: Expr) (state: HangState)
    (inner: FullHungBelow depth)
    (whole: all = read ++ Parse.loopReads [] (linkSteps links))
    (isValue: value = leftNested expr (Parse.stepValues (linkSteps links)))
    (deep: expr.nest1 <= depth)
    (spelt: Spelt expr read)
    (free: expr.autoFree1 = True)
    (lineRead: lineAll read = True)
    (lineAfter: lineAll (Parse.loopReads [] (linkSteps links) ++ rest) = True)
    (openFirst: openHead modes read = True)
    (bound: bounds modes (state.enters read) = True)
    (hung: hangsFrom state (leavesOf (read ++ (Parse.loopReads [] (linkSteps links) ++ rest))) = True)
    (deepItems: deepAll (read ++ (Parse.loopReads [] (linkSteps links) ++ rest)) = True)
    (after: EndsAt modes 16 (Parse.loopReads [] (linkSteps links) ++ rest))
    (linked: LinkReads modes (kind => kind == Plus || kind == Minus) (MulReads (TreeN depth) modes) links rest)
    (high: 16 <= expr.level):
    AddReads (TreeN depth) modes all rest value :=
  ?

--| The `+ -` level.
theorem addHung ∀ (modes: Modes)
    (quiet: Quiet modes)
    (expr: Expr) (read rest: List Item) (depth: Nat) (state: HangState)
    (inner: FullHungBelow depth)
    (deep: expr.nest1 <= depth)
    (spelt: Spelt expr read)
    (free: expr.autoFree1 = True)
    (lineRead: lineAll read = True)
    (lineRest: lineAll rest = True)
    (openFirst: openHead modes read = True)
    (bound: bounds modes (state.enters read) = True)
    (hung: hangsFrom state (leavesOf (read ++ rest)) = True)
    (deepItems: deepAll (read ++ rest) = True)
    (ends: EndsAt modes 14 rest)
    (fits: 14 <= expr.level):
    AddReads (TreeN depth) modes read rest expr :=
  ?

--| The `++` level, nested to the right.
theorem appendHung ∀ (modes: Modes)
    (quiet: Quiet modes)
    (expr: Expr) (read rest: List Item) (depth: Nat) (state: HangState)
    (inner: FullHungBelow depth)
    (deep: expr.nest1 <= depth)
    (spelt: Spelt expr read)
    (free: expr.autoFree1 = True)
    (lineRead: lineAll read = True)
    (lineRest: lineAll rest = True)
    (openFirst: openHead modes read = True)
    (bound: bounds modes (state.enters read) = True)
    (hung: hangsFrom state (leavesOf (read ++ rest)) = True)
    (deepItems: deepAll (read ++ rest) = True)
    (ends: EndsAt modes 12 rest)
    (fits: 12 <= expr.level):
    AppendReads (TreeN depth) modes read rest expr :=
  ?

--| The `++` level, its first operand above it.
theorem appendBaseHung ∀ (modes: Modes)
    (quiet: Quiet modes)
    (expr: Expr) (read rest: List Item) (depth: Nat) (state: HangState)
    (inner: FullHungBelow depth)
    (deep: expr.nest1 <= depth)
    (spelt: Spelt expr read)
    (free: expr.autoFree1 = True)
    (lineRead: lineAll read = True)
    (lineRest: lineAll rest = True)
    (openFirst: openHead modes read = True)
    (bound: bounds modes (state.enters read) = True)
    (hung: hangsFrom state (leavesOf (read ++ rest)) = True)
    (deepItems: deepAll (read ++ rest) = True)
    (ends: EndsAt modes 12 rest)
    (high: 14 <= expr.level):
    AppendReads (TreeN depth) modes read rest expr :=
  ?

--| The comparison level, with no comparison at its top.
theorem cmpAloneHung ∀ (modes: Modes)
    (quiet: Quiet modes)
    (expr: Expr) (read rest: List Item) (depth: Nat) (state: HangState)
    (inner: FullHungBelow depth)
    (deep: expr.nest1 <= depth)
    (spelt: Spelt expr read)
    (free: expr.autoFree1 = True)
    (lineRead: lineAll read = True)
    (lineRest: lineAll rest = True)
    (openFirst: openHead modes read = True)
    (bound: bounds modes (state.enters read) = True)
    (hung: hangsFrom state (leavesOf (read ++ rest)) = True)
    (deepItems: deepAll (read ++ rest) = True)
    (ends: EndsAt modes 6 rest)
    (high: 12 <= expr.level):
    CmpReads (TreeN depth) modes read rest expr :=
  ?

--| The comparison level: two `++` chains joined once.
theorem cmpHung ∀ (modes: Modes)
    (quiet: Quiet modes)
    (expr: Expr) (read rest: List Item) (depth: Nat) (state: HangState)
    (inner: FullHungBelow depth)
    (deep: expr.nest1 <= depth)
    (spelt: Spelt expr read)
    (free: expr.autoFree1 = True)
    (lineRead: lineAll read = True)
    (lineRest: lineAll rest = True)
    (openFirst: openHead modes read = True)
    (bound: bounds modes (state.enters read) = True)
    (hung: hangsFrom state (leavesOf (read ++ rest)) = True)
    (deepItems: deepAll (read ++ rest) = True)
    (ends: EndsAt modes 6 rest)
    (fits: 6 <= expr.level):
    CmpReads (TreeN depth) modes read rest expr :=
  ?
