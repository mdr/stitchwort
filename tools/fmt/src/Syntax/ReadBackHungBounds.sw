--| The line rule against the parser's modes (H2 of SW-4121's plan): an item the rule steps over doesn't stop a
--| reading whose block column the rule bounds (`hungStops`), and the bound carries from one item to the next, into a
--| block and into a bracket.

namespace Syntax.ReadBackHungBounds
import Std (Bool, DecEq, Eq, List, Nat, Option, Result, Text, Void)
import Syntax (..)
import Fmt (..)
import Syntax.ReadBackProofs (..)
import Syntax.ReadBackRuns (..)
import Syntax.ReadBackEnds (wordItem)
import Syntax.ReadBackLine (QuietModes, leadKind)
import Syntax.ReadBackHung (..)

--| A step that gives nothing is no step.
theorem noneNotStep ∀ (state next: HangState) (leaf: Leaf)
    (none: state.step leaf = None)
    (step: state.step leaf = Some next):
    Void :=
  (Option.noneNotSome next (Eq.trans none.flipped step)).impossible

--| A leaf that starts a line, and is no comma, closer or `:=`, is right of the column in force.
theorem stepRight ∀ (state next: HangState) (leaf: Leaf)
    (step: state.step leaf = Some next)
    (starts: leaf.token.lineStart = True)
    (notCloser: leaf.token.kind.isCloser = False)
    (notComma: (leaf.token.kind == Comma) = False)
    (notAssign: (leaf.token.kind == ColonEq) = False):
    inForce state.blocks state.top < leaf.token.column :=
  match right: leaf.token.column > inForce state.blocks state.top with
    | True => right.read
    | False =>
      (noneNotStep state next leaf
        (rewrite starts, notCloser, notComma, notAssign, right then
          match state.glue with
            | True => byComputing
            | False => byComputing)
        step).impossible

--| A false fourth conjunct falsifies the chain.
theorem andFalseExempt ∀ (a c: Bool): (a && True && c && False) = False := cases

--| `deepAll` of one item: a comma or closer has a bracket open.
theorem depthExempt ∀ (item: Item)
    (deep: deepAll [item] = True)
    (exempt: (item.kind == Comma || item.kind.isCloser) = True):
    (item.depth > 0) = True :=
  cases

--| An item the line rule steps over doesn't stop a reading whose limit the rule bounds. A `:=` outside brackets is
--| the exception: the rule lets it start a line anywhere.
theorem hungStops ∀ (modes: Modes) (state next: HangState) (item: Item)
    (quiet: QuietModes modes)
    (bound: bounds modes state = True)
    (stepped: state.step item.leaf = Some next)
    (deep: deepAll [item] = True)
    (inside: (item.kind == ColonEq) = False):
    modes.stops item = False :=
  match limit: modes.limit with
    | None => rewrite quiet.noGuard, quiet.noCalc, quiet.noRule
    | Some column =>
      rewrite quiet.noGuard, quiet.noCalc, quiet.noRule then
        match starts: item.leaf.token.lineStart with
          | False =>
            Bool.andFalseMiddle
              (modes.allow != Some item.index)
              (item.leaf.token.column <= column
                && !((item.kind == Comma || item.kind.isCloser) && item.depth > 0)
                && !(item.leaf.token.column == column && item.kind.isInfixOnly))
          | True =>
            match exempt: item.kind == Comma || item.kind.isCloser with
              | True =>
                let positive := depthExempt item deep exempt
                rewrite positive then andFalseExempt _ _
              | False =>
                let (notComma, notCloser) := Bool.orFalseElim _ _ exempt
                let right := stepRight state next item.leaf stepped starts notCloser notComma inside
                let above: column < item.leaf.token.column := arithmetic
                rewrite Nat.leqFalseOfLess column _ above then Bool.andFalse _

--| The bound depends on the state only through the column in force.
theorem boundsCong ∀ (modes: Modes) (now before: HangState)
    (same: inForce now.blocks now.top = inForce before.blocks before.top)
    (bound: bounds modes before = True):
    bounds modes now = True :=
  match modes.limit with
    | None => byComputing
    | Some limit => rewrite same then bound

--| A step over a leaf that is no closer, comma, `:=` or `:` is what `entered` makes of the state, bracket columns aside.
theorem leafStepPlain ∀ (state next: HangState) (leaf: Leaf)
    (step: state.step leaf = Some next)
    (plain: (leaf.token.kind == Comma
      || leaf.token.kind.isCloser
      || leaf.token.kind == ColonEq
      || leaf.token.kind == Colon)
      = False):
    inForce next.blocks next.top = inForce (state.entered leaf).blocks (state.entered leaf).top :=
  let (notComma, others) := Bool.orFalseElim _ _ plain
  let (notCloser, others2) := Bool.orFalseElim _ _ others
  let (notAssign, notColon) := Bool.orFalseElim _ _ others2
  match glue: state.glue && leaf.token.lineStart with
    | False =>
      match closer: leaf.token.kind.isCloser with
        | False =>
          match comma: leaf.token.kind == Comma with
            | False =>
              match assign: leaf.token.kind == ColonEq with
                | False =>
                  match right: (leaf.token.lineStart.not || inForce state.blocks state.top < leaf.token.column).not with
                    | False =>
                      match colon: leaf.token.kind == Colon with
                        | False =>
                          let same := Option.someInjective step
                          rewrite <- same then
                            match opens: leaf.token.kind.isOpener with
                              | True | False => byComputing

--| After an expression's first leaf, the bound holds of the state it left.
theorem boundsPast ∀ (modes: Modes) (state next: HangState) (item: Item)
    (bound: bounds modes (state.entered item.leaf) = True)
    (stepped: state.step item.leaf = Some next)
    (plain: (item.kind == Comma || item.kind.isCloser || item.kind == ColonEq || item.kind == Colon) = False):
    bounds modes next = True :=
  boundsCong modes next (state.entered item.leaf) (leafStepPlain state next item.leaf stepped plain) bound

--| A block opened at an item that starts its expression and its line bounds the state that item enters.
theorem boundsBlock ∀ (modes: Modes) (state: HangState) (item: Item) (allow: Option Nat) (kind: LineKind)
    (starts: state.start = True)
    (lineStart: item.leaf.token.lineStart = True):
    bounds
      (lineModes (blockModes modes item.leaf.token.column True) item.leaf.token.column True allow kind)
      (state.entered item.leaf)
      = True :=
  rewrite starts, lineStart then match state.blocks with | [] | [_, .._] => arithmetic

--| A kind that leads an expression is no closer, comma or `:=`.
theorem leadNotBracket ∀ (kind: Tok)
    (lead: leadKind kind = True):
    kind.isCloser = False ∧ (kind == Comma) = False ∧ (kind == ColonEq) = False :=
  cases

--| The same item is right of the limit: `BlockAt`'s first clause.
theorem rightOfBound ∀ (modes: Modes) (state next: HangState) (item: Item)
    (bound: bounds modes state = True)
    (stepped: state.step item.leaf = Some next)
    (lineStart: item.leaf.token.lineStart = True)
    (opens: leadKind item.kind = True):
    rightOfLimit item.leaf.token.column modes.limit = True :=
  let (notCloser, notComma, notAssign) := leadNotBracket item.kind opens
  let right := stepRight state next item.leaf stepped lineStart notCloser notComma notAssign
  match modes.limit with
    | None => byComputing
    | Some limit => arithmetic

--| A type on a line of its own: its first leaf, at column 2, is right of the limit 0 the declaration's block holds.
def boundsSource: Text := "def d:\n  A\n  := b\n"

def boundsLeaves: List Leaf := match lex boundsSource with
  | Ok lexed => lexed.leaves
  | Err _ => []

def boundsItem: Item := match (items boundsLeaves).drop 3 with
  | [item, .._] => item
  | [] => wordItem Lower "x" 0

theorem rightOfBoundExample: rightOfLimit boundsItem.leaf.token.column (Some 0) = True :=
  rightOfBound
    { Modes.start | limit = Some 0 }
    { blocks = [], top = None, start = True, glue = False }
    { blocks = [], top = Some 2, start = False, glue = False }
    boundsItem
    byComputing
    byComputing
    byComputing
    byComputing
