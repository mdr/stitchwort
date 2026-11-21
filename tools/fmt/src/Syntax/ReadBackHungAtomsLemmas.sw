--| The line rule's state through a bracket's parts, for H5 of SW-4121's plan: a comma or closer inside a bracket
--| never stops a reading, the bound carries past an expression's first leaf and past a whole spelt expression, and a
--| comma inside a bracket puts the state at the start of the bracket's next item (`HangState.nextItem`).

namespace Syntax.ReadBackHungAtomsLemmas
import Std (Bool, DecEq, Eq, List, Nat, Option, Parse, Void)
import Syntax (..)
import Fmt (..)
import Syntax.ReadBackProofs (..)
import Syntax.ReadBackRuns (..)
import Syntax.ReadBackTree (..)
import Syntax.ReadBackLine (..)
import Syntax.ReadBackHung (..)
import Syntax.ReadBackHungBounds (..)
import Syntax.ReadBackHungFrame (speltEnters, speltHangs)
import Syntax.ReadBackHungFrameLemmas (hangCommaStep, exampleLeaf, leavesOfAppend, infixIsFlat, flatParts)
import Syntax.SharedFacts (commaNotCloser)

--| The line rule over the leaves after the first, from the state the first left.
theorem hungStep ∀ (state: HangState) (leaf: Leaf) (rest: List Leaf)
    (hung: hangsFrom state [leaf, ..rest] = True):
    ∃ (next: HangState) => state.step leaf = Some next ∧ hangsFrom next rest = True :=
  match stepped: state.step leaf with | Some next => (next, byComputing, hung)

--| The line rule over leaves read one after another: the first part leaves a state, from which the rest keep it.
theorem hungSplit ∀ (state: HangState) (first rest: List Leaf)
    (hung: hangsFrom state (first ++ rest) = True):
    ∃ (mid: HangState) => state.after first = Some mid ∧ hangsFrom mid rest = True :=
  let whole: hangsAfter (state.after first) rest = True := rewrite <- hangsFromAppend state first rest then hung
  match after: state.after first with | Some mid => (mid, byComputing, whole)

--| `deepAll` of the head alone.
theorem deepHead ∀ (item: Item) (rest: List Item) (deep: deepAll [item, ..rest] = True): deepAll [item] = True :=
  rewrite Bool.andLeft deep

--| `deepAll` of what follows a part.
theorem deepRest ∀ (first rest: List Item) (deep: deepAll (first ++ rest) = True): deepAll rest = True :=
  match first with
    | [] => deep
    | [item, ..more] => deepRest more rest (Bool.andRight deep)

--| No comma or closer needs a bracket open.
theorem deepOf ∀ (item: Item)
    (notComma: (item.kind == Comma) = False)
    (notCloser: item.kind.isCloser = False):
    deepAll [item] = True :=
  rewrite notComma, notCloser

--| A kind that leads an expression is no closer, comma, `:=` or `:`: the line rule enters the expression at it.
theorem leadPlain ∀ (kind: Tok)
    (lead: leadKind kind = True):
    (kind == Comma || kind.isCloser || kind == ColonEq || kind == Colon) = False :=
  cases

--| A comma or closer inside a bracket stops no reading in quiet modes: the parser's line test exempts it.
theorem deepStops ∀ (modes: Modes) (item: Item)
    (quiet: Quiet modes)
    (deep: deepAll [item] = True)
    (exempt: (item.kind == Comma || item.kind.isCloser) = True):
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
          | True => rewrite exempt, depthExempt item deep exempt then andFalseExempt _ _

--| Entering at a leaf that starts no item and no line keeps the column in force.
theorem enteredSame ∀ (state: HangState) (leaf: Leaf)
    (fresh: (state.start && leaf.token.lineStart) = False):
    inForce (state.entered leaf).blocks (state.entered leaf).top = inForce state.blocks state.top :=
  match state with | { blocks, top, start, glue } => rewrite fresh then cases blocks then byComputing

--| Entering at a leaf that starts an item and its line puts that leaf's column in force.
theorem enteredFresh ∀ (state: HangState) (leaf: Leaf)
    (fresh: (state.start && leaf.token.lineStart) = True):
    inForce (state.entered leaf).blocks (state.entered leaf).top = leaf.token.column :=
  match state with | { blocks, top, start, glue } => rewrite fresh then cases blocks then byComputing

--| The bound holds of a state whose column in force is no further left.
theorem boundsAbove ∀ (modes: Modes) (now before: HangState)
    (above: inForce before.blocks before.top <= inForce now.blocks now.top)
    (bound: bounds modes before = True):
    bounds modes now = True :=
  match modes.limit with
    | None => byComputing
    | Some limit => arithmetic [above]

--| The bound holds of the state an expression's first leaf enters: a leaf that starts a line is right of the column
--| in force.
theorem boundsEntered ∀ (modes: Modes) (state next: HangState) (leaf: Leaf)
    (bound: bounds modes state = True)
    (stepped: state.step leaf = Some next)
    (plain: (leaf.token.kind == Comma
      || leaf.token.kind.isCloser
      || leaf.token.kind == ColonEq
      || leaf.token.kind == Colon)
      = False):
    bounds modes (state.entered leaf) = True :=
  let (notComma, others) := Bool.orFalseElim _ _ plain
  let (notCloser, others2) := Bool.orFalseElim _ _ others
  let (notAssign, _) := Bool.orFalseElim _ _ others2
  match fresh: state.start && leaf.token.lineStart with
    | False => boundsCong modes (state.entered leaf) state (enteredSame state leaf fresh) bound
    | True =>
      let starts: leaf.token.lineStart = True := Bool.andRight fresh
      let right := stepRight state next leaf stepped starts notCloser notComma notAssign
      let above: inForce state.blocks state.top <= inForce (state.entered leaf).blocks (state.entered leaf).top :=
        rewrite enteredFresh state leaf fresh then arithmetic [right]
      boundsAbove modes (state.entered leaf) state above bound

--| An item that leads an expression doesn't stop a reading the state bounds, and leaves a state the bound holds of.
theorem leadHung ∀ (modes: Modes) (state: HangState) (item: Item) (rest: List Item)
    (quiet: Quiet modes)
    (lead: leadKind item.kind = True)
    (bound: bounds modes state = True)
    (hung: hangsFrom state (leavesOf [item, ..rest]) = True):
    modes.stops item = False
      ∧ bounds modes (state.entered item.leaf) = True
      ∧ ∃ (next: HangState) => bounds modes next = True ∧ hangsFrom next (leavesOf rest) = True :=
  let (next, stepped, hungRest) := hungStep state item.leaf (leavesOf rest) hung
  let (notCloser, notComma, notAssign) := leadNotBracket item.kind lead
  let plain := leadPlain item.kind lead
  let entered := boundsEntered modes state next item.leaf bound stepped plain
  (
    hungStops modes state next item quiet bound stepped (deepOf item notComma notCloser) notAssign,
    entered,
    (next, boundsPast modes state next item entered stepped plain, hungRest)
  )

--| After a spelt expression, the line rule is at the state its first leaf entered, which the bound holds of.
theorem speltHung ∀ (modes: Modes) (expr: Expr) (read rest: List Item) (state: HangState)
    (spelt: Spelt expr read)
    (bound: bounds modes state = True)
    (hung: hangsFrom state (leavesOf (read ++ rest)) = True):
    bounds modes (state.enters read) = True ∧ hangsFrom (state.enters read) (leavesOf rest) = True :=
  let (mid, after, hungRest) :=
    hungSplit state (leavesOf read) (leavesOf rest) (rewrite <- leavesOfAppend read rest then hung)
  let isMid := speltEnters expr read spelt state mid after
  let (first, more, isRead, lead) := speltStarts expr read spelt
  let hungFirst: hangsFrom state (leavesOf ([first, ..more] ++ rest)) = True := rewrite <- isRead then hung
  let (next, stepped, _) := hungStep state first.leaf (leavesOf (more ++ rest)) hungFirst
  let entered := boundsEntered modes state next first.leaf bound stepped (leadPlain first.kind lead)
  (rewrite isRead then entered, rewrite <- isMid then hungRest)

--| A comma inside a bracket puts the line rule at the start of the bracket's next item.
theorem commaNext ∀ (state next: HangState) (leaf: Leaf)
    (comma: (leaf.token.kind == Comma) = True)
    (stepped: state.step leaf = Some next):
    next = state.nextItem :=
  match state with
    | { blocks, top, start, glue } =>
      match blocks with
        | [block, ..outer] =>
          hangCommaStep { blocks = [block, ..outer], top, start, glue } next leaf block outer comma byComputing stepped
        | [] =>
          let notCloser := commaNotCloser leaf.token.kind comma
          rewrite notCloser, comma at stepped then cases

--| An item entered at the start of a bracket's item leaves the next item's start where it was.
theorem enteredNext ∀ (state: HangState) (leaf: Leaf) (block: Option Nat) (outer: List (Option Nat))
    (inside: state.blocks = [block, ..outer]):
    (state.entered leaf).nextItem = state.nextItem :=
  match state with | { blocks, top, start, glue } => rewrite inside then cases

--| The start of a bracket's next item, from the start of one, is the same.
theorem nextTwice ∀ (state: HangState): state.nextItem.nextItem = state.nextItem := byComputing

--| After a spelt expression read inside a bracket, the next item's start is the same.
theorem entersNextIn ∀ (expr: Expr) (read: List Item) (state: HangState) (block: Option Nat) (outer: List (Option Nat))
    (inside: state.blocks = [block, ..outer])
    (spelt: Spelt expr read):
    (state.enters read).nextItem = state.nextItem :=
  let (first, more, isRead, _) := speltStarts expr read spelt
  rewrite isRead then enteredNext state first.leaf block outer inside

--| After a spelt expression read from the start of a bracket's item, the next item's start is the same.
theorem entersNext ∀ (expr: Expr) (read: List Item) (state: HangState)
    (spelt: Spelt expr read):
    (state.nextItem.enters read).nextItem = state.nextItem :=
  rewrite entersNextIn expr read state.nextItem None (state.blocks.drop 1) byComputing spelt then nextTwice state

--| No leaf after `->` starts a line.
theorem gluedNoLine ∀ (state: HangState) (leaf: Leaf)
    (glued: state.glue = True)
    (lineStart: leaf.token.lineStart = True):
    state.step leaf = None :=
  match state with | { blocks, top, start, glue } => rewrite glued, lineStart

--| A leaf that starts an item and its line inside a bracket gives that item its column.
theorem freshBlocks ∀ (state: HangState) (leaf: Leaf) (block: Option Nat) (outer: List (Option Nat))
    (starts: state.start = True)
    (lineStart: leaf.token.lineStart = True)
    (inside: state.blocks = [block, ..outer]):
    (state.entered leaf).blocks = [Some leaf.token.column, ..outer] :=
  match state with | { blocks, top, start, glue } => rewrite starts, lineStart, inside

--| A leaf that starts the type or the value and its line, outside brackets, gives it its column.
theorem freshTop ∀ (state: HangState) (leaf: Leaf)
    (starts: state.start = True)
    (lineStart: leaf.token.lineStart = True)
    (outside: state.blocks = []):
    (state.entered leaf).blocks = [] ∧ (state.entered leaf).top = Some leaf.token.column :=
  match state with
    | { blocks, top, start, glue } => ((rewrite starts, lineStart, outside), (rewrite starts, lineStart, outside))

--| After an expression whose first leaf started an item and its line, the line rule lets no leaf take that column's
--| block round again.
theorem freshContinues ∀ (state next: HangState) (leaf after: Leaf)
    (starts: state.start = True)
    (lineStart: leaf.token.lineStart = True)
    (stepped: (state.entered leaf).step after = Some next):
    continuesLeaf leaf.token.column after = False :=
  match state with
    | { blocks, top, start, glue } =>
      match blocks with
        | [block, ..outer] =>
          let placed :=
            freshBlocks { blocks = [block, ..outer], top, start, glue } leaf block outer starts lineStart byComputing
          stepInBracket _ next after leaf.token.column outer placed stepped
        | [] =>
          let (outside, atTop) := freshTop { blocks = [], top, start, glue } leaf starts lineStart byComputing
          stepAtTop _ next after leaf.token.column outside atTop stepped

--| The item after a bracket's first two doesn't stop a reading the state before the second
--| bounds.
theorem peekTwoHung ∀ (modes: Modes)
    (quiet: Quiet modes)
    (first second: Item) (more tail: List Item) (state: HangState)
    (open1: modes.stops first = False)
    (lead: leadKind second.kind = True)
    (bound: bounds modes state = True)
    (hung: hangsFrom state (leavesOf ([second, ..more] ++ tail)) = True)
    (deepItems: deepAll ([second, ..more] ++ tail) = True)
    (tailOpen: openHead modes tail = True)
    (kinds: exprAll more = True)
    (head: exprHead tail = True):
    ∃ (kind: Tok) => peekIn modes 2 [first, second, ..more ++ tail] = Some kind ∧ exprKind kind = True :=
  let (open2, _, (next, nextBound, hungMore)) := leadHung modes state second (more ++ tail) quiet lead bound hung
  match more, kinds with
    | [], _ =>
      match tail, head, tailOpen with
        | [], never, _ => (Bool.falseNotTrue never).impossible
        | [after, ..later], head, tailOpen =>
          (after.kind, (rewrite open1, open2, openHeadStops modes after later tailOpen), head)
    | [third, ..others], kinds =>
      let (next2, stepped, _) := hungStep next third.leaf (leavesOf (others ++ tail)) hungMore
      let deepThird := deepHead third (others ++ tail) (Bool.andRight deepItems)
      let open3 :=
        hungStops modes next next2 third quiet nextBound stepped deepThird
          (exprNotColonEq third.kind (Bool.andLeft kinds))
      (third.kind, (rewrite open1, open2, open3), Bool.andLeft kinds)

--| The items a bracket's first item starts with don't stop a reading the state before
--| it bounds.
theorem speltOutsideHung ∀ (modes: Modes)
    (quiet: Quiet modes)
    (first: Item) (expr: Expr) (read after: List Item) (state: HangState)
    (spelt: Spelt expr read)
    (open1: modes.stops first = False)
    (bound: bounds modes state = True)
    (hung: hangsFrom state (leavesOf (read ++ after)) = True)
    (deepItems: deepAll (read ++ after) = True)
    (afterOpen: openHead modes after = True)
    (afterHead: exprHead after = True):
    parenOutside (peekIn modes 1 [first, ..read ++ after]) (peekIn modes 2 [first, ..read ++ after]) = False :=
  let kinds := speltExpr expr read spelt
  match signed: expr.signed with
    | False =>
      let (second, more, isRead, starts) := speltPlainStarts expr read spelt signed
      let kinds2: exprAll [second, ..more] = True := rewrite <- isRead then kinds
      let hung2: hangsFrom state (leavesOf ([second, ..more] ++ after)) = True := rewrite <- isRead then hung
      let deep2: deepAll ([second, ..more] ++ after) = True := rewrite <- isRead then deepItems
      let lead := startLead second.kind starts
      let (open2, _, _) := leadHung modes state second (more ++ after) quiet lead bound hung2
      let (kind, peek2, kindExpr) :=
        peekTwoHung modes quiet first second more after state open1 lead bound hung2 deep2 afterOpen
          (Bool.andRight kinds2)
          afterHead
      rewrite isRead, quietPeekSecond modes first second (more ++ after) open1 open2, peek2 then
        startOutside second.kind kind starts kindExpr
    | True =>
      match expr, spelt, signed with
        | Prefix _ operand, (sign, more, isRead, isSign, _, _, _, operandSpelt), _ =>
          let hung2: hangsFrom state (leavesOf ([sign, ..more] ++ after)) = True := rewrite <- isRead then hung
          let (open2, _, (next, nextBound, hungMore)) :=
            leadHung modes state sign (more ++ after) quiet (signLead sign.kind isSign) bound hung2
          let (third, others, isMore, thirdLead) := speltStarts operand more operandSpelt
          let hung3: hangsFrom next (leavesOf ([third, ..others] ++ after)) = True := rewrite <- isMore then hungMore
          let (open3, _, _) := leadHung modes next third (others ++ after) quiet thirdLead nextBound hung3
          rewrite isRead, isMore, open1, open2, open3 then signOutside sign.kind third.kind isSign thirdLead
        | App head [_, .._], (headRead, argRead, steps, isRead, fits, _, headSpelt, _), signed =>
          match head, headSpelt, fits, signed with
            | Prefix _ operand, (sign, more, isHead, isSign, _, _, _, operandSpelt), _, _ =>
              let tail := argRead ++ Parse.loopReads [] steps
              let (third, others, isMore, thirdLead) := speltStarts operand more operandSpelt
              let joined: read = [sign, third, ..others ++ tail] := rewrite isRead, isHead, isMore
              let hung2: hangsFrom state (leavesOf ([sign, third, ..others ++ tail] ++ after)) = True :=
                rewrite <- joined then hung
              let (open2, _, (next, nextBound, hungMore)) :=
                leadHung modes state sign
                  ([third, ..others ++ tail] ++ after)
                  quiet
                  (signLead sign.kind isSign)
                  bound
                  hung2
              let (open3, _, _) :=
                leadHung modes next third ((others ++ tail) ++ after) quiet thirdLead nextBound hungMore
              rewrite joined, open1, open2, open3 then signOutside sign.kind third.kind isSign thirdLead
            | App _ _ | Infix _ _ _ _, _, never, _ => (Bool.falseNotTrue never).impossible
            | other, _, _, never => (Bool.falseNotTrue never).impossible
        | App _ [], never, _ => Void.impossible never
        | Infix kind left _ _, (leftRead, arrow, rightRead, isRead, isOp, _, _, _, _, _, leftSpelt, _), _ =>
          let assoc: read ++ after = leftRead ++ ([arrow, ..rightRead] ++ after) :=
            rewrite isRead, List.appendAssoc leftRead [arrow, ..rightRead] after
          let hungLeft: hangsFrom state (leavesOf (leftRead ++ ([arrow, ..rightRead] ++ after))) = True :=
            rewrite <- assoc then hung
          let deepLeft: deepAll (leftRead ++ ([arrow, ..rightRead] ++ after)) = True := rewrite <- assoc then deepItems
          let (leftBound, hungArrow) :=
            speltHung modes left leftRead ([arrow, ..rightRead] ++ after) state leftSpelt bound hungLeft
          let (next, stepped, _) :=
            hungStep (state.enters leftRead) arrow.leaf (leavesOf (rightRead ++ after)) hungArrow
          let (notComma, notCloser, _) := flatParts arrow.kind (infixIsFlat kind arrow.kind isOp)
          let isExpr := infixExpr kind arrow.kind isOp
          let openArrow :=
            hungStops modes
              (state.enters leftRead)
              next
              arrow
              quiet
              leftBound
              stepped
              (deepOf arrow notComma notCloser)
              (exprNotColonEq arrow.kind isExpr)
          rewrite isRead, List.appendAssoc leftRead [arrow, ..rightRead] after then
            speltOutsideHung modes quiet first left leftRead
              ([arrow, ..rightRead] ++ after)
              state
              leftSpelt
              open1
              bound
              hungLeft
              deepLeft
              (openHeadOf modes arrow (rightRead ++ after) openArrow)
              isExpr
        | other, _, never => (Bool.falseNotTrue never).impossible

--| `commaNext`'s hypotheses hold: a comma after a bracket's first item.
theorem commaNextExample: { blocks = [None], top = None, start = True, glue = False }
      = ({ blocks = [None], top = None, start = False, glue = False }: HangState).nextItem :=
  commaNext
    { blocks = [None], top = None, start = False, glue = False }
    { blocks = [None], top = None, start = True, glue = False }
    (exampleLeaf Comma ",")
    byComputing
    byComputing
