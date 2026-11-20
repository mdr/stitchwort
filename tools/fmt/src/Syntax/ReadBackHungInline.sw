--| `&&`, `||`, `->` and the inline expression on any lines (H8 of SW-4121's plan): the logic links, the operator
--| level, an arrow's right side and the inline expression, read from the line rule's state, as in
--| `Syntax.ReadBackHungAtoms`. The arrow is where the line rule's `glue` is used: the
--| leaf after `->` starts no line, so its right side opens no block.

namespace Syntax.ReadBackHungInline
import Std (Bool, DecEq, Eq, List, Nat, Option, Parse, Void)
import Syntax (..)
import Fmt (..)
import Syntax.ReadBackProofs (..)
import Syntax.ReadBackRuns (..)
import Syntax.ReadBackTree (..)
import Syntax.ReadBackEnds (..)
import Syntax.ReadBackLine (..)
import Syntax.AutoPlaced (..)
import Syntax.ReadBackHung (..)
import Syntax.ReadBackHungChains (..)
import Syntax.ReadBackHungAtomsLemmas (leadHung, speltHung, deepRest)
import Syntax.ReadBackHungInlineLemmas (..)

--| `cmpHung` at `depth` in `modes`, as a hypothesis: the logic chain's lemmas take it, so only the operator level,
--| which passes it, is in `cmpHung`'s recursion.
def CmpHungAt (modes: Modes) (depth: Nat): Prop :=
  ∀ (expr: Expr) (read rest: List Item) (state: HangState) => expr.nest <= depth
    → Spelt expr read
    → expr.autoPlaced False = True
    → HungAt modes state read rest
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
  match links, linksSpelt with
    | [], _ => ends.noAndOr (arithmetic [])
    | [(op, read, value), ..later], (andOr, apart, operand, laterSpelt) =>
      let after := Parse.loopReads [] (linkSteps later)
      let (lineRead, lineAfter) := lineSplit read after (Bool.andRight lineLinks)
      let (open, (next, nextBound, hungNext)) :=
        plainHung modes state op ((read ++ after) ++ rest) quiet (andOrPlain op.kind andOr) bound hung
      let hungRead: hangsFrom next (leavesOf (read ++ (after ++ rest))) = True :=
        rewrite <- List.appendAssoc read after rest then hungNext
      let deepNext: deepAll ((read ++ after) ++ rest) = True := Bool.andRight deepItems
      let deepRead: deepAll (read ++ (after ++ rest)) = True :=
        rewrite <- List.appendAssoc read after rest then deepNext
      let (first, more, isRead, starts) := speltStarts value read operand.spelt
      let hungFirst: hangsFrom next (leavesOf ([first, ..more] ++ (after ++ rest))) = True :=
        rewrite <- isRead then hungRead
      let (openFirst, _, _) := leadHung modes next first (more ++ (after ++ rest)) quiet starts nextBound hungFirst
      let peekRead: peekIn modes 0 (read ++ after ++ rest) = Some first.kind :=
        rewrite isRead then peekFirst modes first (more ++ after ++ rest) openFirst
      let (readBound, hungAfter) := speltHung modes value read (after ++ rest) next operand.spelt nextBound hungRead
      (
        open,
        andOr,
        (rewrite peekRead then leadNotExists first.kind starts),
        (rewrite peekRead then leadNotForall first.kind starts),
        cmp value read
          (after ++ rest)
          next
          operand.deep
          operand.spelt
          operand.free
          {
            lineRead = lineRead,
            lineRest = (lineJoin after rest lineAfter lineRest),
            openFirst = (rewrite isRead then openHeadOf modes first more openFirst),
            bound = readBound,
            hung = hungRead,
            deepItems = deepRead
          }
          (linksEndsHung modes quiet depth later rest (next.enters read) laterSpelt readBound hungAfter ends)
          operand.fits,
        logicLinksHung modes quiet depth cmp later rest
          (next.enters read)
          laterSpelt
          lineAfter
          lineRest
          readBound
          hungAfter
          (deepRest read (after ++ rest) deepRead)
          ends
      )

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
  match links, linksSpelt with
    | [], _ => Inl (byComputing, group.flipped, noAndOr)
    | [(op, read, value), ..later], (andOr, _) =>
      let (open, _) :=
        plainHung modes state op
          ((read ++ Parse.loopReads [] (linkSteps later)) ++ rest)
          quiet
          (andOrPlain op.kind andOr)
          bound
          hung
      Inr (
        [(op, read, value), ..later],
        byComputing,
        (rewrite linkValuesLength later then group.flipped),
        (rewrite peekFirst modes op ((read ++ Parse.loopReads [] (linkSteps later)) ++ rest) open then andOr),
        logic
      )

--| An operator expression whose lowest operator is `&&` or `||`.
theorem logicOperatorHung ∀ (modes: Modes)
    (quiet: Quiet modes)
    (expr: Expr) (read read3 rest: List Item) (depth: Nat) (all: List Item) (value: Expr) (state: HangState)
    (cmp: CmpHungAt modes depth)
    (whole: all = read ++ read3)
    (deep: expr.nest <= depth)
    (spelt: Spelt expr read)
    (free: expr.autoPlaced False = True)
    (facts: HungAt modes state read (read3 ++ rest))
    (ends: EndsAt modes 5 (read3 ++ rest))
    (low: 4 <= expr.level)
    (noSection: isSome Dot (peekIn modes 0 ((read ++ read3) ++ rest)) = False)
    (ending: EndReads (TreeN depth) modes expr (sequenceOn modes (read3 ++ rest)) read3 rest value):
    OperatorReads (TreeN depth) modes all rest value :=
  let (first, firstRead, links, isRead, operand, linksSpelt, group) := orFlat depth expr read spelt low free deep
  let linksRead := Parse.loopReads [] (linkSteps links)
  let after := read3 ++ rest
  let (lineFirst, lineLinks) := lineSplit firstRead linksRead (rewrite <- isRead then facts.lineRead)
  let (item, more, isFirst, _) := speltStarts first firstRead operand.spelt
  let openItems: openHead modes ([item, ..more] ++ linksRead) = True :=
    rewrite <- isFirst, <- isRead then facts.openFirst
  let isAll: all = firstRead ++ linksRead ++ read3 :=
    rewrite whole, isRead then List.appendAssoc firstRead linksRead read3
  let hungFirst: hangsFrom state (leavesOf (firstRead ++ (linksRead ++ after))) = True :=
    rewrite <- List.appendAssoc firstRead linksRead after, <- isRead then facts.hung
  let deepFirst: deepAll (firstRead ++ (linksRead ++ after)) = True :=
    rewrite <- List.appendAssoc firstRead linksRead after, <- isRead then facts.deepItems
  let wholeBound: bounds modes (state.enters ([item, ..more] ++ linksRead)) = True :=
    rewrite <- isFirst, <- isRead then facts.bound
  let firstBound: bounds modes (state.enters firstRead) = True := rewrite isFirst then wholeBound
  let hungLinks := speltAfterHung first firstRead (linksRead ++ after) state operand.spelt hungFirst
  let deepLinks := deepRest firstRead (linksRead ++ after) deepFirst
  (
    firstRead,
    linksRead,
    read3,
    first,
    expr,
    isAll,
    (rewrite <- List.appendAssoc firstRead linksRead read3, <- isRead then noSection),
    cmp first firstRead
      (linksRead ++ after)
      state
      operand.deep
      operand.spelt
      operand.free
      {
        lineRead = lineFirst,
        lineRest = (lineJoin linksRead after lineLinks facts.lineRest),
        openFirst = (rewrite isFirst then
          openHeadOf modes item more (openHeadStops modes item (more ++ linksRead) openItems)),
        bound = firstBound,
        hung = hungFirst,
        deepItems = deepFirst
      }
      (linksEndsHung modes quiet depth links after (state.enters firstRead) linksSpelt firstBound hungLinks ends)
      operand.fits,
    logicAfterLinksHung modes quiet depth links after first expr
      (state.enters firstRead)
      linksSpelt
      (group (Succ links.length) (arithmetic []))
      firstBound
      hungLinks
      deepLinks
      (ends.noAndOr (arithmetic []))
      (logicLinksHung modes quiet depth cmp links after
        (state.enters firstRead)
        linksSpelt
        lineLinks
        facts.lineRest
        firstBound
        hungLinks
        deepLinks
        ends),
    ends.noIff,
    ending
  )

--| What `operator` reads: the expression up to an arrow or the end, then what ends it.
theorem operatorHung ∀ (modes: Modes)
    (quiet: Quiet modes)
    (expr: Expr) (read read3 rest: List Item) (depth: Nat) (all: List Item) (value: Expr) (state: HangState)
    (inner: FullHungBelow depth)
    (whole: all = read ++ read3)
    (deep: expr.nest <= depth)
    (spelt: Spelt expr read)
    (free: expr.autoPlaced False = True)
    (facts: HungAt modes state read (read3 ++ rest))
    (ends: EndsAt modes 5 (read3 ++ rest))
    (fits: 2 <= expr.level)
    (noSection: isSome Dot (peekIn modes 0 ((read ++ read3) ++ rest)) = False)
    (ending: EndReads (TreeN depth) modes expr (sequenceOn modes (read3 ++ rest)) read3 rest value):
    OperatorReads (TreeN depth) modes all rest value :=
  logicOperatorHung modes quiet expr read read3 rest depth all value state
    (operand operandRead after operandState operandDeep operandSpelt operandFree facts operandEnds operandFits =>
      cmpHung modes quiet operand operandRead after depth operandState inner operandDeep operandSpelt operandFree facts
          operandEnds operandFits)
    whole
    deep
    spelt
    free
    facts
    ends
    (plainLevel expr read spelt fits)
    noSection
    ending

--| An arrow, its right side read in full one level down: the leaf after `->` starts no line (the line rule's
--| `glue`).
theorem arrowHung ∀ (modes: Modes)
    (quiet: Quiet modes)
    (left right: Expr) (operator: Word) (item: Item) (more rest: List Item) (depth: Nat) (state: HangState)
    (inner: FullHungBelow depth)
    (deep: (Infix InfixArrow left operator right).nest <= depth)
    (spelt: Spelt (Infix InfixArrow left operator right) [item, ..more])
    (free: (Infix InfixArrow left operator right).autoPlaced True = True)
    (lineRead: lineAll [item, ..more] = True)
    (lineRest: lineAll rest = True)
    (open: modes.stops item = False)
    (bound: bounds modes (state.entered item.leaf) = True)
    (hung: hangsFrom state (leavesOf ([item, ..more] ++ rest)) = True)
    (deepItems: deepAll ([item, ..more] ++ rest) = True)
    (ends: endsHere rest = True):
    InlineAt (TreeN depth) modes item more rest (Infix InfixArrow left operator right) :=
  let (leftRead, arrow, rightRead, isRead, isOp, isWord, _, leftFits, _, apart, leftSpelt, rightSpelt) := spelt
  let isArrow: arrow.kind = Arrow := DecEq.sound isOp
  let (first, inside, isLeft, starts) := speltStarts left leftRead leftSpelt
  let joined: [item, ..more] = [first, ..inside ++ [arrow, ..rightRead]] := calc [item, ..more]
    _ = leftRead ++ [arrow, ..rightRead] := isRead
    _ = [first, ..inside ++ [arrow, ..rightRead]] := rewrite isLeft
  let isItem: item = first := List.consInjectiveHead joined
  let itemLead: leadKind item.kind = True := rewrite isItem then starts
  let (lineLeft, lineOpRight) := lineSplit leftRead [arrow, ..rightRead] (rewrite <- isRead then lineRead)
  let lineRight: lineAll rightRead = True := Bool.andRight lineOpRight
  let after := rightRead ++ rest
  let lineAfterLeft: lineAll [arrow, ..after] = True := lineJoin [arrow, ..rightRead] rest lineOpRight lineRest
  let shape: [item, ..more] ++ rest = leftRead ++ ([arrow, ..rightRead] ++ rest) :=
    rewrite isRead then List.appendAssoc leftRead [arrow, ..rightRead] rest
  let hungLeft: hangsFrom state (leavesOf (leftRead ++ ([arrow, ..rightRead] ++ rest))) = True :=
    rewrite <- shape then hung
  let deepLeft: deepAll (leftRead ++ ([arrow, ..rightRead] ++ rest)) = True := rewrite <- shape then deepItems
  let deepRight: deepAll (rightRead ++ rest) = True :=
    Bool.andRight (deepRest leftRead ([arrow, ..rightRead] ++ rest) deepLeft)
  let leftBound: bounds modes (state.enters leftRead) = True := rewrite isLeft, <- isItem then bound
  let (openOp, (next, glued, nextBound, hungRight)) :=
    arrowHungParts modes quiet left leftRead arrow rightRead rest state leftSpelt isOp leftBound hungLeft
  let openLeft: openHead modes leftRead = True := rewrite isLeft, <- isItem then openHeadOf modes item inside open
  let peekArrow: peekIn modes 0 [arrow, ..after] = Some Arrow := rewrite peekFirst modes arrow after openOp, isArrow
  let (rightFirst, rightMore, isRight, rightStarts) := speltStarts right rightRead rightSpelt
  let hungRightItems: hangsFrom next (leavesOf ([rightFirst, ..rightMore] ++ rest)) = True :=
    rewrite <- isRight then hungRight
  let (openRight, _, _) := leadHung modes next rightFirst (rightMore ++ rest) quiet rightStarts nextBound hungRightItems
  let allowed: allowBraceOn modes (rightRead ++ rest) = modes :=
    rewrite isRight then allowNoBrace modes rightFirst (rightMore ++ rest) (startNotBrace rightFirst.kind rightStarts)
  let noRow: rowOn
    (isSome LBrace (peekIn (allowBraceOn modes (rightRead ++ rest)) 0 (rightRead ++ rest)))
    (rightRead ++ rest)
    = False :=
    rewrite allowed,
        isRight,
        peekFirst modes rightFirst (rightMore ++ rest) openRight,
        startNotBrace rightFirst.kind rightStarts
  match depth, deep with
    | Zero, deep => Void.impossible (arithmetic [deep])
    | Succ below, deep =>
      let sub := TreeN (Succ below)
      let leftEnds: EndsAt modes 5 [arrow, ..after] :=
        opEnds modes 5 arrow after InfixArrow openOp isOp
          (rewrite speltApart right rightRead rest rightSpelt then apart)
          (rewrite isArrow then arithmetic [])
      let rightTree: sub { modes = allowBraceOn modes (rightRead ++ rest), level = LevelFull } rightRead rest right :=
        rewrite allowed then
          inner below
            (arithmetic [])
            modes
            right
            rightRead
            rest
            next
            quiet
            (arithmetic [deep])
            rightSpelt
            (Bool.andRight free)
            lineRight
            lineRest
            (Inr glued)
            nextBound
            hungRight
            deepRight
            ends
      let ending: EndReads sub modes left
        (sequenceOn modes ([arrow, ..rightRead] ++ rest))
        [arrow, ..rightRead]
        rest
        (Infix InfixArrow left operator right) :=
        Inr (arrow, rightRead, right, byComputing, (rewrite isWord), openOp, isArrow, (noRow, rightTree))
      let noSection: isSome Dot (peekIn modes 0 ((leftRead ++ [arrow, ..rightRead]) ++ rest)) = False :=
        rewrite <- isRead, peekFirst modes item (more ++ rest) open then leadNotDot item.kind itemLead
      let operatorReads: OperatorReads sub modes [item, ..more] rest (Infix InfixArrow left operator right) :=
        operatorHung modes quiet left leftRead
          [arrow, ..rightRead]
          rest
          (Succ below)
          [item, ..more]
          (Infix InfixArrow left operator right)
          state
          inner
          isRead
          (arithmetic [deep])
          leftSpelt
          (autoPlacedInner left (Bool.andLeft free))
          {
            lineRead = lineLeft,
            lineRest = lineAfterLeft,
            openFirst = openLeft,
            bound = leftBound,
            hung = hungLeft,
            deepItems = deepLeft
          }
          leftEnds
          leftFits
          noSection
          ending
      (
        open,
        inlinePlainOf modes item
          (more ++ rest)
          (linePlain [item, ..more ++ rest] (lineJoin [item, ..more] rest lineRead lineRest))
          (noAutoLine (Infix InfixArrow left operator right) item more rest spelt free)
          (noWalkLine modes (Infix InfixArrow left operator right) item more rest spelt),
        operatorReads
      )

--| An inline expression with no arrow at its top.
theorem inlinePlainHung ∀ (modes: Modes)
    (quiet: Quiet modes)
    (expr: Expr) (item: Item) (more rest: List Item) (depth: Nat) (state: HangState)
    (inner: FullHungBelow depth)
    (deep: expr.nest <= depth)
    (spelt: Spelt expr [item, ..more])
    (free: expr.autoPlaced True = True)
    (lineRead: lineAll [item, ..more] = True)
    (lineRest: lineAll rest = True)
    (open: modes.stops item = False)
    (bound: bounds modes (state.entered item.leaf) = True)
    (hung: hangsFrom state (leavesOf ([item, ..more] ++ rest)) = True)
    (deepItems: deepAll ([item, ..more] ++ rest) = True)
    (ends: endsHere rest = True)
    (fits: 2 <= expr.level):
    InlineAt (TreeN depth) modes item more rest expr :=
  let restEnds := endsAtOf modes 1 rest ends
  let (first, inside, isRead, starts) := speltStarts expr [item, ..more] spelt
  let itemLead: leadKind item.kind = True := rewrite firstKind item first more inside isRead then starts
  let noSection: isSome Dot (peekIn modes 0 (([item, ..more] ++ []) ++ rest)) = False :=
    rewrite List.appendNil [item, ..more], peekFirst modes item (more ++ rest) open then leadNotDot item.kind itemLead
  let operatorReads: OperatorReads (TreeN depth) modes [item, ..more] rest expr :=
    operatorHung modes quiet expr
      [item, ..more]
      []
      rest
      depth
      [item, ..more]
      expr
      state
      inner
      (List.appendNil [item, ..more]).flipped
      deep
      spelt
      (autoPlacedInner expr free)
      {
        lineRead = lineRead,
        lineRest = lineRest,
        openFirst = (openHeadOf modes item more open),
        bound = bound,
        hung = hung,
        deepItems = deepItems
      }
      (endsAtUp modes 1 5 rest (arithmetic []) restEnds)
      fits
      noSection
      (Inl (byComputing, byComputing, restEnds.noEnd (arithmetic [])))
  (
    open,
    inlinePlainOf modes item
      (more ++ rest)
      (linePlain [item, ..more ++ rest] (lineJoin [item, ..more] rest lineRead lineRest))
      (noAutoLine expr item more rest spelt free)
      (noWalkLine modes expr item more rest spelt),
    operatorReads
  )

--| The inline expression, what `expr` reads where its first item starts no block: from the state before the first
--| item, with the modes' limit bounded against the state that item enters, and the line rule over the items and what
--| follows. `open` stays: the first item is the caller's
--| to place (a block's own first item is allowed by its modes, not by its column).
theorem inlineHung ∀ (modes: Modes)
    (quiet: Quiet modes)
    (expr: Expr) (item: Item) (more rest: List Item) (depth: Nat) (state: HangState)
    (inner: FullHungBelow depth)
    (deep: expr.nest <= depth)
    (spelt: Spelt expr [item, ..more])
    (free: expr.autoPlaced True = True)
    (lineRead: lineAll [item, ..more] = True)
    (lineRest: lineAll rest = True)
    (open: modes.stops item = False)
    (bound: bounds modes (state.entered item.leaf) = True)
    (hung: hangsFrom state (leavesOf ([item, ..more] ++ rest)) = True)
    (deepItems: deepAll ([item, ..more] ++ rest) = True)
    (ends: endsHere rest = True):
    InlineAt (TreeN depth) modes item more rest expr :=
  match expr, spelt with
    | Infix InfixArrow left operator right, spelt =>
      arrowHung modes quiet left right operator item more rest depth state inner deep spelt free lineRead lineRest open
          bound hung deepItems ends
    | Infix InfixBinary left operator right, spelt =>
      let (_, op, _, _, isOp, _, level, _) := spelt
      inlinePlainHung modes quiet
        (Infix InfixBinary left operator right)
        item
        more
        rest
        depth
        state
        inner
        deep
        spelt
        free
        lineRead
        lineRest
        open
        bound
        hung
        deepItems
        ends
        (arithmetic [level, binaryAboveArrow op.kind isOp])
    | Infix _ _ _ _, (_, _, _, _, never, _) => (Bool.falseNotTrue never).impossible
    | other, spelt =>
      inlinePlainHung modes quiet other item more rest depth state inner deep spelt free lineRead lineRest open bound
          hung deepItems ends
          (arithmetic [unaryLevel other [item, ..more] spelt byComputing])
