--| The binary chains on any lines (H7 of SW-4121's plan): `* / %`, `+ -`, `++` and a comparison, read from the line
--| rule's state, as in `Syntax.ReadBackHungAtoms`. The accumulators' line rule runs over the operand and the links
--| after it.

namespace Syntax.ReadBackHungChains
import Std (Bool, List, Nat, Option, Parse, Void)
import Syntax (..)
import Fmt (..)
import Syntax.ReadBackProofs (..)
import Syntax.ReadBackRuns (..)
import Syntax.ReadBackTree (..)
import Syntax.ReadBackEnds (..)
import Syntax.ReadBackLine (..)
import Syntax.AutoPlaced (..)
import Syntax.ReadBackHung (..)
import Syntax.ReadBackHungApp (..)
import Syntax.ReadBackHungChainsLemmas (..)

--| `* / %` links after a first operand, nested to the left.
theorem mulAccHung ∀ (modes: Modes)
    (quiet: QuietModes modes)
    (expr: Expr) (read: List Item) (links: List (Item, List Item, Expr)) (rest: List Item) (depth: Nat) (all: List Item)
    (value: Expr) (state: HangState)
    (inner: FullHungBelow depth)
    (whole: all = read ++ Parse.loopReads [] (linkSteps links))
    (isValue: value = leftNested expr (Parse.stepValues (linkSteps links)))
    (deep: expr.nest <= depth)
    (spelt: Spelt expr read)
    (free: expr.autoPlaced False = True)
    (facts: HungAt modes state read (Parse.loopReads [] (linkSteps links) ++ rest))
    (after: UnaryEnds modes (Parse.loopReads [] (linkSteps links) ++ rest))
    (linked: LinkReads modes
      (kind => kind == Star || kind == Slash || kind == Percent)
      (UnaryReads (TreeN depth) modes)
      links
      rest)
    (fits: 16 <= expr.level):
    MulReads (TreeN depth) modes all rest value :=
  match unary: expr.unary with
    | True => (
      read,
      expr,
      links,
      whole,
      isValue,
      unaryHung modes quiet expr read
        (Parse.loopReads [] (linkSteps links) ++ rest)
        depth
        state
        inner
        deep
        spelt
        free
        facts
        after
        unary,
      linked
    )
    | False =>
      match expr, spelt, unary, fits with
        | Infix InfixBinary left operator right, (leftRead, op, rightRead, isRead, isOp, isWord, level, leftFits,
            rightFits, apart, leftSpelt, rightSpelt), _, fits =>
          let rightAfter := Parse.loopReads [] (linkSteps links) ++ rest
          let hungL: hangsFrom state (leavesOf (leftRead ++ ([op, ..rightRead] ++ rightAfter))) = True :=
            rewrite <- List.appendAssoc leftRead [op, ..rightRead] rightAfter, <- isRead then facts.hung
          let deepL: deepAll (leftRead ++ ([op, ..rightRead] ++ rightAfter)) = True :=
            rewrite <- List.appendAssoc leftRead [op, ..rightRead] rightAfter, <- isRead then facts.deepItems
          let (after1, parts) :=
            hungParts modes quiet InfixBinary left right leftRead op rightRead rightAfter state leftSpelt rightSpelt
                isOp
                (rewrite <- isRead then facts.lineRead)
                (rewrite <- isRead then facts.openFirst)
                (rewrite <- isRead then facts.bound)
                hungL
                deepL
          let at16: infixLevel InfixBinary operator.text = 16 := arithmetic [fits, level, binaryAtMost op.kind isOp]
          let (leftNeed, rightNeed) := mulNeeds operator.text at16
          let isMul := mulOf op.kind isOp (arithmetic [at16, level])
          let rightReads: UnaryReads (TreeN depth) modes rightRead rightAfter right :=
            unaryHung modes quiet right rightRead rightAfter depth after1 inner
              (arithmetic [deep])
              rightSpelt
              (Bool.andRight free)
              {
                lineRead = (Bool.andRight parts.lineOpRight),
                lineRest = facts.lineRest,
                openFirst = parts.openRight,
                bound = parts.boundRight,
                hung = parts.hungRight,
                deepItems = parts.deepRight
              }
              after
              (highUnary right rightRead rightSpelt (arithmetic [rightFits, rightNeed]))
          let tail := [(op, rightRead, right), ..links]
          let lineTail: lineAll (Parse.loopReads [] (linkSteps tail) ++ rest) = True :=
            rewrite List.appendAssoc rightRead (Parse.loopReads [] (linkSteps links)) rest then
              lineJoin [op, ..rightRead] rightAfter parts.lineOpRight facts.lineRest
          let afterTail: UnaryEnds modes (Parse.loopReads [] (linkSteps tail) ++ rest) :=
            rewrite List.appendAssoc rightRead (Parse.loopReads [] (linkSteps links)) rest then
              (opEnds modes 17 op
                (rightRead ++ rightAfter)
                InfixBinary
                parts.openOp
                isOp
                (rewrite speltApart right rightRead rightAfter rightSpelt then apart)
                (arithmetic [rungMulOf op.kind isMul])).unary
          let wholeTail: all = leftRead ++ Parse.loopReads [] (linkSteps tail) :=
            rewrite whole, isRead then
              List.appendAssoc leftRead [op, ..rightRead] (Parse.loopReads [] (linkSteps links))
          let valueTail: value = leftNested left (Parse.stepValues (linkSteps tail)) := rewrite isValue, isWord
          mulAccHung modes quiet left leftRead tail rest depth all value state inner wholeTail valueTail
            (arithmetic [deep])
            leftSpelt
            (Bool.andLeft free)
            {
              lineRead = parts.lineLeft,
              lineRest = lineTail,
              openFirst = parts.openLeft,
              bound = parts.boundLeft,
              hung = (rewrite List.appendAssoc rightRead (Parse.loopReads [] (linkSteps links)) rest then hungL),
              deepItems = (rewrite List.appendAssoc rightRead (Parse.loopReads [] (linkSteps links)) rest then deepL)
            }
            afterTail
            (parts.openOp, isMul, rightReads, linked)
            (arithmetic [leftFits, leftNeed])
        | Infix InfixArrow _ _ _, _, _, fits => Void.impossible (arithmetic [fits])
        | Infix _ _ _ _, (_, _, _, _, never, _), _, _ => (Bool.falseNotTrue never).impossible
        | _, _, never, _ => (Bool.falseNotTrue never.flipped).impossible

--| The `* / %` level.
theorem mulHung ∀ (modes: Modes)
    (quiet: QuietModes modes)
    (expr: Expr) (read rest: List Item) (depth: Nat) (state: HangState)
    (inner: FullHungBelow depth)
    (deep: expr.nest <= depth)
    (spelt: Spelt expr read)
    (free: expr.autoPlaced False = True)
    (facts: HungAt modes state read rest)
    (ends: EndsAt modes 16 rest)
    (fits: 16 <= expr.level):
    MulReads (TreeN depth) modes read rest expr :=
  mulAccHung modes quiet expr read [] rest depth read expr state inner
    (List.appendNil read).flipped
    byComputing
    deep
    spelt
    free
    facts
    ends.unary
    (ends.noMul (arithmetic []))
    fits

--| `+ -` links after a first operand of the `+` level, nested to the left.
theorem addAccHung ∀ (modes: Modes)
    (quiet: QuietModes modes)
    (expr: Expr) (read: List Item) (links: List (Item, List Item, Expr)) (rest: List Item) (depth: Nat) (all: List Item)
    (value: Expr) (state: HangState)
    (inner: FullHungBelow depth)
    (whole: all = read ++ Parse.loopReads [] (linkSteps links))
    (isValue: value = leftNested expr (Parse.stepValues (linkSteps links)))
    (deep: expr.nest <= depth)
    (spelt: Spelt expr read)
    (free: expr.autoPlaced False = True)
    (facts: HungAt modes state read (Parse.loopReads [] (linkSteps links) ++ rest))
    (after: EndsAt modes 16 (Parse.loopReads [] (linkSteps links) ++ rest))
    (linked: LinkReads modes (kind => kind == Plus || kind == Minus) (MulReads (TreeN depth) modes) links rest)
    (fits: 14 <= expr.level):
    AddReads (TreeN depth) modes all rest value :=
  match expr, spelt, fits with
    | Infix InfixBinary left operator right, sp, fits =>
      let (leftRead, op, rightRead, isRead, isOp, isWord, level, leftFits, rightFits, apart, leftSpelt, rightSpelt) :=
        sp
      match binaryLow op.kind isOp (arithmetic [fits, level]) with
        | Inr is16 =>
          addBaseHung modes quiet
            (Infix InfixBinary left operator right)
            read
            links
            rest
            depth
            all
            value
            state
            inner
            whole
            isValue
            deep
            sp
            free
            facts
            after
            linked
            (arithmetic [level, is16])
        | Inl is14 =>
          let rightAfter := Parse.loopReads [] (linkSteps links) ++ rest
          let hungL: hangsFrom state (leavesOf (leftRead ++ ([op, ..rightRead] ++ rightAfter))) = True :=
            rewrite <- List.appendAssoc leftRead [op, ..rightRead] rightAfter, <- isRead then facts.hung
          let deepL: deepAll (leftRead ++ ([op, ..rightRead] ++ rightAfter)) = True :=
            rewrite <- List.appendAssoc leftRead [op, ..rightRead] rightAfter, <- isRead then facts.deepItems
          let (after1, parts) :=
            hungParts modes quiet InfixBinary left right leftRead op rightRead rightAfter state leftSpelt rightSpelt
                isOp
                (rewrite <- isRead then facts.lineRead)
                (rewrite <- isRead then facts.openFirst)
                (rewrite <- isRead then facts.bound)
                hungL
                deepL
          let at14: infixLevel InfixBinary operator.text = 14 := arithmetic [level, is14]
          let (leftNeed, rightNeed) := addNeeds operator.text at14
          let isAdd := addOf op.kind isOp is14
          let rightReads: MulReads (TreeN depth) modes rightRead rightAfter right :=
            mulHung modes quiet right rightRead rightAfter depth after1 inner
              (arithmetic [deep])
              rightSpelt
              (Bool.andRight free)
              {
                lineRead = (Bool.andRight parts.lineOpRight),
                lineRest = facts.lineRest,
                openFirst = parts.openRight,
                bound = parts.boundRight,
                hung = parts.hungRight,
                deepItems = parts.deepRight
              }
              after
              (arithmetic [rightFits, rightNeed])
          let tail := [(op, rightRead, right), ..links]
          let lineTail: lineAll (Parse.loopReads [] (linkSteps tail) ++ rest) = True :=
            rewrite List.appendAssoc rightRead (Parse.loopReads [] (linkSteps links)) rest then
              lineJoin [op, ..rightRead] rightAfter parts.lineOpRight facts.lineRest
          let afterTail: EndsAt modes 16 (Parse.loopReads [] (linkSteps tail) ++ rest) :=
            rewrite List.appendAssoc rightRead (Parse.loopReads [] (linkSteps links)) rest then
              opEnds modes 16 op
                (rightRead ++ rightAfter)
                InfixBinary
                parts.openOp
                isOp
                (rewrite speltApart right rightRead rightAfter rightSpelt then apart)
                (arithmetic [rungAddOf op.kind isAdd])
          let wholeTail: all = leftRead ++ Parse.loopReads [] (linkSteps tail) :=
            rewrite whole, isRead then
              List.appendAssoc leftRead [op, ..rightRead] (Parse.loopReads [] (linkSteps links))
          let valueTail: value = leftNested left (Parse.stepValues (linkSteps tail)) := rewrite isValue, isWord
          addAccHung modes quiet left leftRead tail rest depth all value state inner wholeTail valueTail
            (arithmetic [deep])
            leftSpelt
            (Bool.andLeft free)
            {
              lineRead = parts.lineLeft,
              lineRest = lineTail,
              openFirst = parts.openLeft,
              bound = parts.boundLeft,
              hung = (rewrite List.appendAssoc rightRead (Parse.loopReads [] (linkSteps links)) rest then hungL),
              deepItems = (rewrite List.appendAssoc rightRead (Parse.loopReads [] (linkSteps links)) rest then deepL)
            }
            afterTail
            (parts.openOp, isAdd, rightReads, linked)
            (arithmetic [leftFits, leftNeed])
    | Infix InfixArrow _ _ _, _, fits => Void.impossible (arithmetic [fits])
    | Infix _ _ _ _, (_, _, _, _, never, _), _ => (Bool.falseNotTrue never).impossible
    | other, spelt, _ =>
      addBaseHung modes quiet other read links rest depth all value state inner whole isValue deep spelt free facts
          after linked
          (arithmetic [unaryLevel other read spelt byComputing])

--| `+ -` links after a first operand above the `+` level.
theorem addBaseHung ∀ (modes: Modes)
    (quiet: QuietModes modes)
    (expr: Expr) (read: List Item) (links: List (Item, List Item, Expr)) (rest: List Item) (depth: Nat) (all: List Item)
    (value: Expr) (state: HangState)
    (inner: FullHungBelow depth)
    (whole: all = read ++ Parse.loopReads [] (linkSteps links))
    (isValue: value = leftNested expr (Parse.stepValues (linkSteps links)))
    (deep: expr.nest <= depth)
    (spelt: Spelt expr read)
    (free: expr.autoPlaced False = True)
    (facts: HungAt modes state read (Parse.loopReads [] (linkSteps links) ++ rest))
    (after: EndsAt modes 16 (Parse.loopReads [] (linkSteps links) ++ rest))
    (linked: LinkReads modes (kind => kind == Plus || kind == Minus) (MulReads (TreeN depth) modes) links rest)
    (high: 16 <= expr.level):
    AddReads (TreeN depth) modes all rest value :=
  (
    read,
    expr,
    links,
    whole,
    isValue,
    mulHung modes quiet expr read
      (Parse.loopReads [] (linkSteps links) ++ rest)
      depth
      state
      inner
      deep
      spelt
      free
      facts
      after
      high,
    linked
  )

--| The `+ -` level.
theorem addHung ∀ (modes: Modes)
    (quiet: QuietModes modes)
    (expr: Expr) (read rest: List Item) (depth: Nat) (state: HangState)
    (inner: FullHungBelow depth)
    (deep: expr.nest <= depth)
    (spelt: Spelt expr read)
    (free: expr.autoPlaced False = True)
    (facts: HungAt modes state read rest)
    (ends: EndsAt modes 14 rest)
    (fits: 14 <= expr.level):
    AddReads (TreeN depth) modes read rest expr :=
  addAccHung modes quiet expr read [] rest depth read expr state inner
    (List.appendNil read).flipped
    byComputing
    deep
    spelt
    free
    facts
    (endsAtUp modes 14 16 rest (arithmetic []) ends)
    (ends.noAdd (arithmetic []))
    fits

--| The `++` level, nested to the right.
theorem appendHung ∀ (modes: Modes)
    (quiet: QuietModes modes)
    (expr: Expr) (read rest: List Item) (depth: Nat) (state: HangState)
    (inner: FullHungBelow depth)
    (deep: expr.nest <= depth)
    (spelt: Spelt expr read)
    (free: expr.autoPlaced False = True)
    (facts: HungAt modes state read rest)
    (ends: EndsAt modes 12 rest)
    (fits: 12 <= expr.level):
    AppendReads (TreeN depth) modes read rest expr :=
  match expr, spelt, fits with
    | Infix InfixBinary left operator right, sp, fits =>
      let (leftRead, op, rightRead, isRead, isOp, isWord, level, leftFits, rightFits, apart, leftSpelt, rightSpelt) :=
        sp
      match binaryAppend op.kind isOp (arithmetic [fits, level]) with
        | Inr high =>
          appendBaseHung modes quiet
            (Infix InfixBinary left operator right)
            read
            rest
            depth
            state
            inner
            deep
            sp
            free
            facts
            ends
            (arithmetic [level, high])
        | Inl is12 =>
          let hungL: hangsFrom state (leavesOf (leftRead ++ ([op, ..rightRead] ++ rest))) = True :=
            rewrite <- List.appendAssoc leftRead [op, ..rightRead] rest, <- isRead then facts.hung
          let deepL: deepAll (leftRead ++ ([op, ..rightRead] ++ rest)) = True :=
            rewrite <- List.appendAssoc leftRead [op, ..rightRead] rest, <- isRead then facts.deepItems
          let (after1, parts) :=
            hungParts modes quiet InfixBinary left right leftRead op rightRead rest state leftSpelt rightSpelt isOp
              (rewrite <- isRead then facts.lineRead)
              (rewrite <- isRead then facts.openFirst)
              (rewrite <- isRead then facts.bound)
              hungL
              deepL
          let at12: infixLevel InfixBinary operator.text = 12 := arithmetic [level, is12]
          let (leftNeed, rightNeed) := appendNeeds operator.text at12
          let isAppend := appendOf op.kind isOp is12
          let rightReads: AppendReads (TreeN depth) modes rightRead rest right :=
            appendHung modes quiet right rightRead rest depth after1 inner
              (arithmetic [deep])
              rightSpelt
              (Bool.andRight free)
              {
                lineRead = (Bool.andRight parts.lineOpRight),
                lineRest = facts.lineRest,
                openFirst = parts.openRight,
                bound = parts.boundRight,
                hung = parts.hungRight,
                deepItems = parts.deepRight
              }
              ends
              (arithmetic [rightFits, rightNeed])
          let leftReads: AddReads (TreeN depth) modes leftRead ([op, ..rightRead] ++ rest) left :=
            addHung modes quiet left leftRead
              ([op, ..rightRead] ++ rest)
              depth
              state
              inner
              (arithmetic [deep])
              leftSpelt
              (Bool.andLeft free)
              {
                lineRead = parts.lineLeft,
                lineRest = (lineJoin [op, ..rightRead] rest parts.lineOpRight facts.lineRest),
                openFirst = parts.openLeft,
                bound = parts.boundLeft,
                hung = hungL,
                deepItems = deepL
              }
              (opEnds modes 14 op
                (rightRead ++ rest)
                InfixBinary
                parts.openOp
                isOp
                (rewrite speltApart right rightRead rest rightSpelt then apart)
                (arithmetic [rungAppendOf op.kind isAppend]))
              (arithmetic [leftFits, leftNeed])
          rightCons modes
            (kind => kind == PlusPlus)
            (AddReads (TreeN depth) modes)
            leftRead
            op
            rightRead
            rest
            left
            right
            read
            (Infix InfixBinary left operator right)
            isRead
            (rewrite isWord)
            leftReads
            parts.openOp
            isAppend
            rightReads
    | Infix InfixArrow _ _ _, _, fits => Void.impossible (arithmetic [fits])
    | Infix _ _ _ _, (_, _, _, _, never, _), _ => (Bool.falseNotTrue never).impossible
    | other, spelt, _ =>
      appendBaseHung modes quiet other read rest depth state inner deep spelt free facts ends
        (arithmetic [unaryLevel other read spelt byComputing])

--| The `++` level, its first operand above it.
theorem appendBaseHung ∀ (modes: Modes)
    (quiet: QuietModes modes)
    (expr: Expr) (read rest: List Item) (depth: Nat) (state: HangState)
    (inner: FullHungBelow depth)
    (deep: expr.nest <= depth)
    (spelt: Spelt expr read)
    (free: expr.autoPlaced False = True)
    (facts: HungAt modes state read rest)
    (ends: EndsAt modes 12 rest)
    (high: 14 <= expr.level):
    AppendReads (TreeN depth) modes read rest expr :=
  (
    read,
    expr,
    [],
    (List.appendNil read).flipped,
    byComputing,
    addHung modes quiet expr read rest depth state inner deep spelt free facts
      (endsAtUp modes 12 14 rest (arithmetic []) ends)
      high,
    ends.noAppend (arithmetic [])
  )

--| The comparison level, with no comparison at its top.
theorem cmpAloneHung ∀ (modes: Modes)
    (quiet: QuietModes modes)
    (expr: Expr) (read rest: List Item) (depth: Nat) (state: HangState)
    (inner: FullHungBelow depth)
    (deep: expr.nest <= depth)
    (spelt: Spelt expr read)
    (free: expr.autoPlaced False = True)
    (facts: HungAt modes state read rest)
    (ends: EndsAt modes 6 rest)
    (high: 12 <= expr.level):
    CmpReads (TreeN depth) modes read rest expr :=
  Inl (
    (
      ends.noRange,
      ends.noPipe,
      appendHung modes quiet expr read rest depth state inner deep spelt free facts
        (endsAtUp modes 6 12 rest (arithmetic []) ends)
        high
    ),
    ends.noCmp (arithmetic [])
  )

--| The comparison level: two `++` chains joined once.
theorem cmpHung ∀ (modes: Modes)
    (quiet: QuietModes modes)
    (expr: Expr) (read rest: List Item) (depth: Nat) (state: HangState)
    (inner: FullHungBelow depth)
    (deep: expr.nest <= depth)
    (spelt: Spelt expr read)
    (free: expr.autoPlaced False = True)
    (facts: HungAt modes state read rest)
    (ends: EndsAt modes 6 rest)
    (fits: 6 <= expr.level):
    CmpReads (TreeN depth) modes read rest expr :=
  match expr, spelt, fits with
    | Infix InfixBinary left operator right, sp, fits =>
      let (leftRead, op, rightRead, isRead, isOp, isWord, level, leftFits, rightFits, apart, leftSpelt, rightSpelt) :=
        sp
      match binaryCmp op.kind isOp (arithmetic [fits, level]) with
        | Inr high =>
          cmpAloneHung modes quiet
            (Infix InfixBinary left operator right)
            read
            rest
            depth
            state
            inner
            deep
            sp
            free
            facts
            ends
            (arithmetic [level, high])
        | Inl is6 =>
          let hungL: hangsFrom state (leavesOf (leftRead ++ ([op, ..rightRead] ++ rest))) = True :=
            rewrite <- List.appendAssoc leftRead [op, ..rightRead] rest, <- isRead then facts.hung
          let deepL: deepAll (leftRead ++ ([op, ..rightRead] ++ rest)) = True :=
            rewrite <- List.appendAssoc leftRead [op, ..rightRead] rest, <- isRead then facts.deepItems
          let (after1, parts) :=
            hungParts modes quiet InfixBinary left right leftRead op rightRead rest state leftSpelt rightSpelt isOp
              (rewrite <- isRead then facts.lineRead)
              (rewrite <- isRead then facts.openFirst)
              (rewrite <- isRead then facts.bound)
              hungL
              deepL
          let at6: infixLevel InfixBinary operator.text = 6 := arithmetic [level, is6]
          let (leftNeed, rightNeed) := cmpNeeds operator.text at6
          let (isCmp, notIn) := cmpOf op.kind isOp is6
          let leftEnds: EndsAt modes 12 [op, ..rightRead ++ rest] :=
            opEnds modes 12 op
              (rightRead ++ rest)
              InfixBinary
              parts.openOp
              isOp
              (rewrite speltApart right rightRead rest rightSpelt then apart)
              (arithmetic [rungCmpOf op.kind isCmp])
          let leftReads: AppendReads (TreeN depth) modes leftRead ([op, ..rightRead] ++ rest) left :=
            appendHung modes quiet left leftRead
              ([op, ..rightRead] ++ rest)
              depth
              state
              inner
              (arithmetic [deep])
              leftSpelt
              (Bool.andLeft free)
              {
                lineRead = parts.lineLeft,
                lineRest = (lineJoin [op, ..rightRead] rest parts.lineOpRight facts.lineRest),
                openFirst = parts.openLeft,
                bound = parts.boundLeft,
                hung = hungL,
                deepItems = deepL
              }
              leftEnds
              (aboveCmp left leftRead leftSpelt (arithmetic [leftFits, leftNeed]))
          let rightReads: AppendReads (TreeN depth) modes rightRead rest right :=
            appendHung modes quiet right rightRead rest depth after1 inner
              (arithmetic [deep])
              rightSpelt
              (Bool.andRight free)
              {
                lineRead = (Bool.andRight parts.lineOpRight),
                lineRest = facts.lineRest,
                openFirst = parts.openRight,
                bound = parts.boundRight,
                hung = parts.hungRight,
                deepItems = parts.deepRight
              }
              (endsAtUp modes 6 12 rest (arithmetic []) ends)
              (aboveCmp right rightRead rightSpelt (arithmetic [rightFits, rightNeed]))
          let (rightFirst, rightMore, isRight, rightStarts) := speltStarts right rightRead rightSpelt
          let openRead: openHead modes rightRead = True := parts.openRight
          let openRightFirst: modes.stops rightFirst = False :=
            openHeadStops modes rightFirst rightMore (rewrite isRight at openRead then openRead)
          let noIf: isSome KwIf (peekIn modes 0 (rightRead ++ rest)) = False :=
            rewrite isRight, peekFirst modes rightFirst (rightMore ++ rest) openRightFirst then
              leadNotIf rightFirst.kind rightStarts
          Inr (
            leftRead,
            op,
            rightRead,
            left,
            right,
            isRead,
            (rewrite isWord),
            (leftEnds.noRange, leftEnds.noPipe, leftReads),
            parts.openOp,
            notIn,
            isCmp,
            noIf,
            (ends.noRange, ends.noPipe, rightReads),
            ends.noCmp (arithmetic [])
          )
    | Infix InfixArrow _ _ _, _, fits => Void.impossible (arithmetic [fits])
    | Infix _ _ _ _, (_, _, _, _, never, _), _ => (Bool.falseNotTrue never).impossible
    | other, spelt, _ =>
      cmpAloneHung modes quiet other read rest depth state inner deep spelt free facts ends
        (arithmetic [unaryLevel other read spelt byComputing])
