--| Calls and signs on any lines (H6 of SW-4121's plan): `signArgLine`, `argumentLine`, `argsLine`, `appLine`,
--| `headLine`, `appAny` and `unaryLine` with the line rule's state in place of "starts no line", as in
--| `Syntax.ReadBackHungAtoms`.

namespace Syntax.ReadBackHungApp
import Std (Bool, List, Nat, Option, Parse)
import Syntax (..)
import Fmt (..)
import Syntax.ReadBackProofs (..)
import Syntax.ReadBackRuns (..)
import Syntax.ReadBackTree (..)
import Syntax.ReadBackEnds (..)
import Syntax.ReadBackLine (..)
import Syntax.ReadBackHung (..)
import Syntax.ReadBackHungAtoms (..)

--| A sign glued to an atom, as a call's argument.
theorem signArgHung ∀ (modes: Modes)
    (quiet: Quiet modes)
    (operator: Word) (operand: Expr) (read later: List Item) (depth: Nat) (state: HangState)
    (inner: FullHungBelow depth)
    (deep: (Prefix operator operand).nest1 <= depth)
    (spelt: Spelt (Prefix operator operand) read)
    (atomic: operand.atomic1 = True)
    (glue: argumentGlue read = True)
    (free: operand.autoFree1 = True)
    (lineRead: lineAll read = True)
    (lineLater: lineAll later = True)
    (bound: bounds modes (state.enters read) = True)
    (hung: hangsFrom state (leavesOf (read ++ later)) = True)
    (deepItems: deepAll (read ++ later) = True)
    (after: ∀ (kind: Tok) => AtomEnds modes False kind later):
    AtomReads (TreeN depth) modes False read later (Prefix operator operand) :=
  ?

--| One argument of a call.
theorem argumentHung ∀ (modes: Modes)
    (quiet: Quiet modes)
    (argument: Expr) (read later: List Item) (below: Nat) (state: HangState)
    (inner: FullHungBelow (Succ below))
    (deep: argument.nest1 <= below)
    (spelt: Spelt argument read)
    (fits: argumentFits argument read = True)
    (free: argument.autoFree1 = True)
    (lineRead: lineAll read = True)
    (lineLater: lineAll later = True)
    (bound: bounds modes (state.enters read) = True)
    (hung: hangsFrom state (leavesOf (read ++ later)) = True)
    (deepItems: deepAll (read ++ later) = True)
    (after: ∀ (kind: Tok) => AtomEnds modes False kind later):
    ArgumentReads (TreeN (Succ below)) modes read later argument :=
  ?

--| A call's arguments after the first: `state` is the line rule's before the first of them.
theorem argsHung ∀ (modes: Modes)
    (quiet: Quiet modes)
    (exprs: List Expr) (steps: List (List Item, Expr)) (rest: List Item) (below: Nat) (state: HangState)
    (inner: FullHungBelow (Succ below))
    (deep: nestAll exprs <= below)
    (spelt: SpeltArgs exprs steps)
    (free: autoFreeAll exprs = True)
    (lineSteps: lineAll (Parse.loopReads [] steps) = True)
    (lineRest: lineAll rest = True)
    (bound: bounds modes state = True)
    (hung: hangsFrom state (leavesOf (Parse.loopReads [] steps ++ rest)) = True)
    (deepItems: deepAll (Parse.loopReads [] steps ++ rest) = True)
    (ends: UnaryEnds modes rest):
    ArgsReads (TreeN (Succ below)) modes steps rest :=
  ?

--| A call.
theorem appHung ∀ (modes: Modes)
    (quiet: Quiet modes)
    (head argument: Expr) (more: List Expr) (read rest: List Item) (depth: Nat) (state: HangState)
    (inner: FullHungBelow depth)
    (deep: (App head [argument, ..more]).nest1 <= depth)
    (spelt: Spelt (App head [argument, ..more]) read)
    (free: (App head [argument, ..more]).autoFree1 = True)
    (lineRead: lineAll read = True)
    (lineRest: lineAll rest = True)
    (openFirst: openHead modes read = True)
    (bound: bounds modes (state.enters read) = True)
    (hung: hangsFrom state (leavesOf (read ++ rest)) = True)
    (deepItems: deepAll (read ++ rest) = True)
    (ends: UnaryEnds modes rest):
    AppReads (TreeN depth) modes read rest (App head [argument, ..more]) :=
  ?

--| A call's head.
theorem headHung ∀ (modes: Modes)
    (quiet: Quiet modes)
    (head: Expr) (read later: List Item) (depth: Nat) (state: HangState)
    (inner: FullHungBelow depth)
    (deep: head.nest1 <= depth)
    (spelt: Spelt head read)
    (fits: headFits head read = True)
    (free: head.autoFree1 = True)
    (lineRead: lineAll read = True)
    (lineLater: lineAll later = True)
    (openRead: openHead modes read = True)
    (bound: bounds modes (state.enters read) = True)
    (hung: hangsFrom state (leavesOf (read ++ later)) = True)
    (deepItems: deepAll (read ++ later) = True)
    (after: ∀ (kind: Tok) => AtomEnds modes True kind later):
    AtomReads (TreeN depth) modes True read later head :=
  ?

--| A call or an atom, unsigned.
theorem appAnyHung ∀ (modes: Modes)
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
    (ends: UnaryEnds modes rest)
    (unsigned: expr.signed1 = False)
    (plain: expr.unary1 = True):
    AppReads (TreeN depth) modes read rest expr :=
  ?

--| The unary level: a sign and its operand, or a call.
theorem unaryHung ∀ (modes: Modes)
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
    (ends: UnaryEnds modes rest)
    (unary: expr.unary1 = True):
    UnaryReads (TreeN depth) modes read rest expr :=
  ?
