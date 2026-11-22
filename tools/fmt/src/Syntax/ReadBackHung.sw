--| Slice 1's read-back over any number of lines (SW-4121): the definitions the hung family shares. A declaration's
--| items parse back to the tree they spell when their leaves keep the line rule `Fmt.hangs`; the lemmas carry the line
--| rule's state (`HangState`); what they share with the parser's spelling is in `Syntax.ReadBackLine`.
--|
--| The family is split by layer so that its lemmas can be proved side by side: the state lemmas
--| (`Syntax.ReadBackHungDeep`, `ReadBackHungBounds`, `ReadBackHungFrame`), then the rungs from atoms up
--| (`ReadBackHungAtoms`, `ReadBackHungApp`, `ReadBackHungChains`, `ReadBackHungInline`), the full expression
--| (`ReadBackHungFull`), and the declaration (`ReadBackHungTop`, `readsBackHung`). The reading recurses through
--| brackets from atoms back to full expressions; that recursion is cut by a hypothesis, `FullHungBelow`:
--| each rung at `depth` takes `fullHung` at every smaller depth, and `ReadBackHungTop` ties the knot by induction on
--| the depth.

namespace Syntax.ReadBackHung
import Std (Bool, List, Nat, Option)
import Syntax (..)
import Fmt (..)
import Syntax.ReadBackProofs (..)
import Syntax.ReadBackRuns (..)
import Syntax.ReadBackTree (..)
import Syntax.ReadBackEnds (..)
import Syntax.ReadBackLine (..)
import Syntax.AutoPlaced (..)

--| The leaves of items.
def leavesOf (read: List Item): List Leaf := read.map (item => item.leaf)

--| Every closer and comma is inside a bracket, where `stopsByLine` lets it start a line.
def deepAll: List Item → Bool
  | [] => True
  | [item, ..rest] => (!(item.kind == Comma || item.kind.isCloser) || item.depth > 0) && deepAll rest

--| The parser's block column is no further right than the line rule's column in force.
def bounds (modes: Modes) (state: HangState): Bool := match modes.limit with
  | Some limit => limit <= inForce state.blocks state.top
  | None => True

--| The state an expression is read under once its first leaf has placed it: the column recorded if that leaf
--| starts the expression and its line; no longer at a start, nor after `->`.
def HangState.entered (state: HangState) (first: Leaf): HangState :=
  let fresh := state.start && first.token.lineStart
  {
    blocks = startBlocks fresh first.token.column state.blocks,
    top = startTop fresh first.token.column state.blocks state.top,
    start = False,
    glue = False
  }

--| `entered` by the first of some items, if any: the rungs that take their items whole bound their modes by it.
def HangState.enters (state: HangState): List Item → HangState
  | [] => state
  | [item, .._] => state.entered item.leaf

--| The state at the start of a bracket's next item: what the line rule makes of a comma (`HangState.step`), the
--| current item's column dropped. The bracket's lemmas over the items after the first bound their modes by it.
def HangState.nextItem (state: HangState): HangState :=
  { blocks = [None, ..state.blocks.drop 1], top = state.top, start = True, glue = False }

--| The six facts the rungs of the read-back ladder (`atomHung` up to `operatorHung`) take about `read`, the items of the
--| expression being read, and `rest`, the items that follow it (for a chain's later links, `rest` is those links and
--| what follows), when `state` is the line rule's state before them: both are `lineAll` (`lineRead`, `lineRest`);
--| `read`'s first item stops no reading at `modes` (`openFirst`, `openHead`); `modes` bounds the state `read`'s first
--| item enters (`bound`); the rule hangs every leaf of `read ++ rest` from `state` (`hung`); and every closer and comma
--| of `read ++ rest` is inside a bracket (`deepItems`, `deepAll`).
type HungAt (modes: Modes) (state: HangState) (read rest: List Item) = {
  lineRead: lineAll read = True,
  lineRest: lineAll rest = True,
  openFirst: openHead modes read = True,
  bound: bounds modes (state.enters read) = True,
  hung: hangsFrom state (leavesOf (read ++ rest)) = True,
  deepItems: deepAll (read ++ rest) = True
}

--| `fullHung` at `depth`, as a hypothesis: what `expr` reads, on any lines, of an expression nested at most `depth`
--| deep. The statement is `Syntax.ReadBackHungTop.fullHung`'s.
def FullHungAt (depth: Nat): Prop :=
  ∀ (modes: Modes) (expr: Expr) (read rest: List Item) (state: HangState) => QuietModes modes
    → expr.nest <= depth
    → Spelt expr read
    → expr.autoPlaced True = True
    → lineAll read = True
    → lineAll rest = True
    → (state.start = True ∨ state.glue = True)
    → bounds modes state = True
    → hangsFrom state (leavesOf (read ++ rest)) = True
    → deepAll (read ++ rest) = True
    → endsHere rest = True
    → FullReads (TreeN depth) modes read rest expr

--| `fullHung` at every depth below `depth`: what a rung at `depth` takes for the expressions inside its brackets,
--| and for an arrow's right side.
def FullHungBelow (depth: Nat): Prop := ∀ (smaller: Nat) => smaller < depth → FullHungAt smaller
