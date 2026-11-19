--| Atoms and brackets on any lines (H5 of SW-4121's plan): `atomLine`, `tupleSteps`, `listSteps` and `openSteps`
--| with the line rule's state in place of "starts no line". Each is today's statement with `laterInLine` (or
--| `inLineAll`) replaced by the state before the first item (`state`), the modes' limit bounded against the state that
--| item enters (`bound`), the line rule over the items and what follows (`hung`), every closer and comma inside a
--| bracket (`deepItems`), and `fullHung` below the depth (`inner`) for the expressions inside the brackets.

namespace Syntax.ReadBackHungAtoms
import Std (Bool, List, Nat, Option, Parse)
import Syntax (..)
import Fmt (..)
import Syntax.ReadBackProofs (..)
import Syntax.ReadBackRuns (..)
import Syntax.ReadBackTree (..)
import Syntax.ReadBackEnds (..)
import Syntax.ReadBackLine (..)
import Syntax.ReadBackHung (..)

--| A spelt expression is what `atom` reads, on any lines the line rule allows.
theorem atomHung ∀ (modes: Modes)
    (quiet: Quiet modes)
    (head: Bool) (expr: Expr) (read rest: List Item) (depth: Nat) (state: HangState)
    (inner: FullHungBelow depth)
    (deep: expr.nest1 <= depth)
    (spelt: Spelt expr read)
    (atomic: expr.atomic1 = True)
    (free: expr.autoFree1 = True)
    (lineRead: lineAll read = True)
    (lineRest: lineAll rest = True)
    (openFirst: openHead modes read = True)
    (bound: bounds modes (state.enters read) = True)
    (hung: hangsFrom state (leavesOf (read ++ rest)) = True)
    (deepItems: deepAll (read ++ rest) = True)
    (after: ∀ (kind: Tok) => AtomEnds modes head kind rest):
    AtomReads (TreeN depth) modes head read rest expr :=
  ?

--| A tuple's items after the first two, each after its comma, then the closer: `state` is the line rule's before the
--| first comma, and the modes are bounded at the start of a bracket's item (`nextItem`).
theorem tupleStepsHung ∀ (modes: Modes)
    (quiet: Quiet modes)
    (exprs: List Expr) (steps: List (Item, List Item, Expr)) (count: Nat) (last: Item) (rest: List Item)
    (depth: Nat) (state: HangState)
    (inner: FullHungBelow (Succ depth))
    (deep: nestAll exprs <= depth)
    (spelt: SpeltSteps exprs steps)
    (free: autoFreeAll exprs = True)
    (lineSteps: lineAll (commaReads steps) = True)
    (lineRest: lineAll [last, ..rest] = True)
    (bound: bounds modes state.nextItem = True)
    (hung: hangsFrom state (leavesOf (commaReads steps ++ [last, ..rest])) = True)
    (deepItems: deepAll (commaReads steps ++ [last, ..rest]) = True)
    (isClose: last.kind = RParen):
    CommaReads modes (tupleEnds modes) (TreeN (Succ depth) { modes, level = LevelFull }) count steps [last, ..rest] :=
  ?

--| A list's items after the first, likewise.
theorem listStepsHung ∀ (modes: Modes)
    (quiet: Quiet modes)
    (exprs: List Expr) (steps: List (Item, List Item, Expr)) (count: Nat) (last: Item) (rest: List Item)
    (depth: Nat) (state: HangState)
    (inner: FullHungBelow (Succ depth))
    (deep: nestAll exprs <= depth)
    (spelt: SpeltSteps exprs steps)
    (free: autoFreeAll exprs = True)
    (lineSteps: lineAll (commaReads steps) = True)
    (lineRest: lineAll [last, ..rest] = True)
    (bound: bounds modes state.nextItem = True)
    (hung: hangsFrom state (leavesOf (commaReads steps ++ [last, ..rest])) = True)
    (deepItems: deepAll (commaReads steps ++ [last, ..rest]) = True)
    (isClose: last.kind = RBracket):
    CommaReads modes (count => modes.at RBracket) (ListElement (TreeN (Succ depth)) modes) count steps [last, ..rest] :=
  ?

--| After a bracket's items, the next comma or the closer doesn't stop a reading: each is inside the bracket
--| (`deepItems`), and no comma starts a line.
theorem openStepsHung ∀ (modes: Modes)
    (quiet: Quiet modes)
    (steps: List (Item, List Item, Expr)) (last: Item) (rest: List Item) (state: HangState)
    (hung: hangsFrom state (leavesOf ((commaReads steps ++ [last]) ++ rest)) = True)
    (deepItems: deepAll ((commaReads steps ++ [last]) ++ rest) = True):
    openHead modes ((commaReads steps ++ [last]) ++ rest) = True :=
  ?
