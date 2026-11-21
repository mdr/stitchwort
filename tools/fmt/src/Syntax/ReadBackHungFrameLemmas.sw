--| What the line rule's step does to a state, by the kind of leaf (SW-4142, H3 of SW-4121's plan): the lemmas
--| `speltHangs` needs, one for each kind of leaf an expression is spelt with.

namespace Syntax.ReadBackHungFrameLemmas
import Std (Bool, List, Nat, Option)
import Syntax (..)
import Fmt (..)
import Syntax.ReadBackProofs (..)
import Syntax.ReadBackLine (..)
import Syntax.ReadBackHung (..)
import Fmt.HangProofs (staleBlocks)
import Syntax.SharedFacts (commaNotCloser)

--| Whether a token kind is a bracket, a comma, `:=` or `:`: the kinds a flat leaf is not.
def breaksFlat (kind: Tok): Bool := kind == Comma || kind.isCloser || kind == ColonEq || kind == Colon || kind.isOpener

--| An atom's kind is no bracket, comma, `:=` or `:`.
theorem wordIsFlat ∀ (kind: Tok)
    (word: kind.wordWithin1 = True):
    (kind == Comma || kind.isCloser || kind == ColonEq || kind == Colon || kind.isOpener) = False :=
  cases

theorem signIsFlat ∀ (kind: Tok)
    (signed: signKind kind = True):
    (kind == Comma || kind.isCloser || kind == ColonEq || kind == Colon || kind.isOpener) = False :=
  cases

theorem infixIsFlat ∀ (kind: InfixKind) (tok: Tok)
    (isOp: infixTok kind tok = True):
    (tok == Comma || tok.isCloser || tok == ColonEq || tok == Colon || tok.isOpener) = False :=
  cases

theorem wordIsNoArrow ∀ (kind: Tok) (word: kind.wordWithin1 = True): (kind == Arrow) = False := cases

theorem signIsNoArrow ∀ (kind: Tok) (signed: signKind kind = True): (kind == Arrow) = False := cases

theorem flatParts ∀ (kind: Tok)
    (flat: breaksFlat kind = False):
    (kind == Comma) = False
      ∧ kind.isCloser = False
      ∧ (kind == ColonEq) = False
      ∧ (kind == Colon) = False
      ∧ kind.isOpener = False :=
  cases

--| A leaf that is no bracket, comma, `:=` or `:` and no `->`, stepped over from a state, enters it: the state its
--| expression's first leaf placed.
theorem flatStep ∀ (state next: HangState) (leaf: Leaf)
    (flat: breaksFlat leaf.token.kind = False)
    (noArrow: (leaf.token.kind == Arrow) = False)
    (stepped: state.step leaf = Some next):
    next = state.entered leaf :=
  let (notComma, notCloser, notColonEq, notColon, notOpener) := flatParts leaf.token.kind flat
  match state with
    | { blocks, top, start, glue } =>
      rewrite notComma, notCloser, notColonEq, notColon, notOpener, noArrow at stepped then cases

theorem openerParts ∀ (kind: Tok)
    (opener: kind.isOpener = True):
    (kind == Comma) = False
      ∧ kind.isCloser = False
      ∧ (kind == ColonEq) = False
      ∧ (kind == Colon) = False
      ∧ (kind == Arrow) = False :=
  cases

--| An opener enters the state its expression's first leaf places, and starts the bracket's first item.
theorem hangOpenStep ∀ (state next: HangState) (leaf: Leaf)
    (opener: leaf.token.kind.isOpener = True)
    (stepped: state.step leaf = Some next):
    next
      = {
        blocks = [None, ..(state.entered leaf).blocks],
        top = (state.entered leaf).top,
        start = True,
        glue = False
      } :=
  let (notComma, notCloser, notColonEq, notColon, notArrow) := openerParts leaf.token.kind opener
  match state with
    | { blocks, top, start, glue } =>
      rewrite notComma, notCloser, notColonEq, notColon, opener, notArrow at stepped then cases

--| A closer ends the bracket: the state is the one outside it.
theorem closeStep ∀ (state next: HangState) (leaf: Leaf) (block: Option Nat) (outer: List (Option Nat))
    (closer: leaf.token.kind.isCloser = True)
    (inside: state.blocks = [block, ..outer])
    (stepped: state.step leaf = Some next):
    next = { blocks = outer, top = state.top, start = False, glue = False } :=
  match state with | { blocks, top, start, glue } => rewrite inside, closer at stepped then cases

--| A comma starts the bracket's next item.
theorem hangCommaStep ∀ (state next: HangState) (leaf: Leaf) (block: Option Nat) (outer: List (Option Nat))
    (comma: (leaf.token.kind == Comma) = True)
    (inside: state.blocks = [block, ..outer])
    (stepped: state.step leaf = Some next):
    next = { blocks = [None, ..outer], top = state.top, start = True, glue = False } :=
  let notCloser := commaNotCloser leaf.token.kind comma
  match state with | { blocks, top, start, glue } => rewrite inside, comma, notCloser at stepped then cases

theorem leavesOfAppend ∀ (xs ys: List Item): leavesOf (xs ++ ys) = leavesOf xs ++ leavesOf ys :=
  List.mapAppend xs ys (item => item.leaf)

--| `HangState.after` of what comes after a state that may have broken the rule.
def thenAfter (state: Option HangState) (leaves: List Leaf): Option HangState := match state with
  | Some known => known.after leaves
  | None => None

--| The line rule over two parts of leaves, the second from where the first left it.
theorem afterAppend ∀ (state: HangState) (first rest: List Leaf):
    state.after (first ++ rest) = thenAfter (state.after first) rest :=
  match first with
    | [] => byComputing
    | [leaf, ..more] =>
      match stepped: state.step leaf with
        | Some next => afterAppend next more rest
        | None => byComputing

--| An idle state (no item to start, no `->` to glue) is entered by any leaf as it already is.
theorem enteredIdle ∀ (state: HangState) (leaf: Leaf)
    (idle: state.start = False):
    state.entered leaf = { blocks = state.blocks, top = state.top, start = False, glue = False } :=
  match state with | { blocks, top, start, glue } => rewrite idle then cases

--| An idle state stepped over a flat leaf that is no `->` keeps its columns.
theorem idleStep ∀ (state next: HangState) (leaf: Leaf)
    (idle: state.start = False)
    (flat: breaksFlat leaf.token.kind = False)
    (noArrow: (leaf.token.kind == Arrow) = False)
    (stepped: state.step leaf = Some next):
    next = { blocks = state.blocks, top = state.top, start = False, glue = False } :=
  let (notComma, notCloser, notColonEq, notColon, notOpener) := flatParts leaf.token.kind flat
  match state, idle with
    | { blocks, top, start = False, glue }, _ =>
      rewrite notComma, notCloser, notColonEq, notColon, notOpener, noArrow at stepped then
        rewrite staleBlocks leaf.token.column blocks at stepped then cases

--| The same over `->`, which glues the next leaf to it.
theorem idleArrow ∀ (state next: HangState) (leaf: Leaf)
    (idle: state.start = False)
    (flat: breaksFlat leaf.token.kind = False)
    (arrow: (leaf.token.kind == Arrow) = True)
    (stepped: state.step leaf = Some next):
    next = { blocks = state.blocks, top = state.top, start = False, glue = True } :=
  let (notComma, notCloser, notColonEq, notColon, notOpener) := flatParts leaf.token.kind flat
  match state, idle with
    | { blocks, top, start = False, glue }, _ =>
      rewrite notComma, notCloser, notColonEq, notColon, notOpener, arrow at stepped then
        rewrite staleBlocks leaf.token.column blocks at stepped then cases

--| Inside a bracket (its item's block over the outer ones), a leaf's entry replaces the item's block and keeps the
--| outer ones and the type's or body's column.
theorem enteredBracketed ∀ (state: HangState) (leaf: Leaf) (block: Option Nat)
    (outer: List (Option Nat)) (top: Option Nat)
    (isBlocks: state.blocks = [block, ..outer])
    (isTop: state.top = top):
    ∃ (placed: Option Nat) => (state.entered leaf).blocks = [placed, ..outer] ∧ (state.entered leaf).top = top :=
  (
    if state.start && leaf.token.lineStart then Some leaf.token.column else block,
    match state with | { blocks, top = above, start, glue } => rewrite isBlocks then cases,
    match state with | { blocks, top = above, start, glue } => rewrite isBlocks, isTop then cases
  )

--| A state entered by a leaf is idle, so a later entry leaves it as it is.
theorem enteredTwice ∀ (state: HangState) (first later: Leaf):
    (state.entered first).entered later = state.entered first :=
  rewrite enteredIdle (state.entered first) later byComputing

--| Entering by the first of some items, after a first leaf has entered, changes nothing.
theorem entersSame ∀ (state: HangState) (first: Leaf) (read: List Item):
    (state.entered first).enters read = state.entered first :=
  match read with
    | [] => byComputing
    | [item, .._] => enteredTwice state first item.leaf

--| A state inside a bracket whose first leaf was entered from outside it: the bracket's item block over the outer
--| ones, and the type's or body's column.
def Within (state entered: HangState): Prop :=
  ∃ (placed: Option Nat) => state.blocks = [placed, ..entered.blocks] ∧ state.top = entered.top

--| An opener's step puts the state inside the bracket it opens.
theorem openWithin ∀ (state next: HangState) (leaf: Leaf)
    (opener: leaf.token.kind.isOpener = True)
    (stepped: state.step leaf = Some next):
    Within next (state.entered leaf) :=
  rewrite hangOpenStep state next leaf opener stepped then (None, byComputing, byComputing)

--| Entering a state by some items' first keeps it inside the bracket.
theorem entersWithin ∀ (state entered: HangState) (read: List Item)
    (within: Within state entered):
    Within (state.enters read) entered :=
  match read with
    | [] => within
    | [item, .._] =>
      let (placed, isBlocks, isTop) := within
      enteredBracketed state item.leaf placed entered.blocks entered.top isBlocks isTop

--| A comma inside a bracket starts its next item, still inside the bracket.
theorem commaWithin ∀ (state next entered: HangState) (leaf: Leaf)
    (within: Within state entered)
    (comma: (leaf.token.kind == Comma) = True)
    (stepped: state.step leaf = Some next):
    Within next entered :=
  let (placed, isBlocks, isTop) := within
  rewrite hangCommaStep state next leaf placed entered.blocks comma isBlocks stepped then (None, byComputing, isTop)

--| A closer ends the bracket that a leaf opened: the state is the one that leaf entered.
theorem closerEntered ∀ (state inside next: HangState) (first last: Leaf)
    (closer: last.token.kind.isCloser = True)
    (within: Within inside (state.entered first))
    (stepped: inside.step last = Some next):
    next = state.entered first :=
  let (placed, isBlocks, isTop) := within
  rewrite closeStep inside next last placed (state.entered first).blocks closer isBlocks stepped, isTop

--| An operator or sign between two leaves of one expression, stepped over by the state the first entered, leaves
--| the next leaf's entry as the first's.
theorem afterOperator ∀ (state next: HangState) (first op later: Leaf)
    (flat: breaksFlat op.token.kind = False)
    (stepped: (state.entered first).step op = Some next):
    next.entered later = state.entered first :=
  match e: op.token.kind == Arrow with
    | True =>
      let n := idleArrow (state.entered first) next op byComputing flat e stepped
      let idle: next.start = False := rewrite n
      rewrite enteredIdle next later idle, n
    | False =>
      let n := idleStep (state.entered first) next op byComputing flat e stepped
      let idle: next.start = False := rewrite n
      rewrite enteredIdle next later idle, n

--| The line rule over a first leaf and the rest: the first leaf's step, then the rest from its state.
theorem afterCons ∀ (state next: HangState) (leaf: Leaf) (rest: List Leaf)
    (after: state.after [leaf, ..rest] = Some next):
    ∃ (mid: HangState) => state.step leaf = Some mid ∧ mid.after rest = Some next :=
  match stepped: state.step leaf with | Some mid => (mid, stepped, after)

--| The line rule over two parts of leaves: the first from the state, the second from where the first left it.
theorem afterSplit ∀ (state next: HangState) (first rest: List Leaf)
    (after: state.after (first ++ rest) = Some next):
    ∃ (mid: HangState) => state.after first = Some mid ∧ mid.after rest = Some next :=
  match e: state.after first with
    | Some mid => (mid, e, rewrite afterAppend state first rest, e at after then after)
    | None => rewrite afterAppend state first rest, e at after then cases

theorem afterNil ∀ (state next: HangState) (after: state.after [] = Some next): next = state := cases

theorem afterOne ∀ (state next: HangState) (leaf: Leaf)
    (after: state.after [leaf] = Some next):
    state.step leaf = Some next :=
  match state.step leaf with | Some mid => after

def exampleLeaf (kind: Tok) (text: Text): Leaf :=
  { token = { kind, text, column = 2, lineStart = False }, trivia = Trivia.empty }

--| `hangOpenStep`'s hypotheses hold: a `(` at column 2 inside the type, as the first item of a bracket.
theorem openStepExample: { blocks = [None], top = None, start = True, glue = False }
      = { blocks = [None, ..[]], top = None, start = True, glue = False } :=
  hangOpenStep
    { blocks = [], top = None, start = True, glue = False }
    { blocks = [None], top = None, start = True, glue = False }
    (exampleLeaf LParen "(")
    byComputing
    byComputing

--| `closeStep`'s: a `)` ends a bracket whose item has no block.
theorem closeStepExample: { blocks = [], top = None, start = False, glue = False }
      = { blocks = [], top = None, start = False, glue = False } :=
  closeStep
    { blocks = [None], top = None, start = False, glue = False }
    { blocks = [], top = None, start = False, glue = False }
    (exampleLeaf RParen ")")
    None
    []
    byComputing
    byComputing
    byComputing
