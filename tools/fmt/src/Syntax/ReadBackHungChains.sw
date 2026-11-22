--| The binary chains on any lines (H7 of SW-4121's plan): `* / %`, `+ -`, `++` and a comparison, read from the line
--| rule's state, as in `Syntax.ReadBackHungAtoms`. The accumulators' line rule runs over the operand and the links
--| after it.

namespace Syntax.ReadBackHungChains
import Std (Bool, Eq, List, Nat, Option, Parse, Void)
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
          withWitness _
            (chainStep modes quiet InfixBinary left right read leftRead op rightRead links rest state leftSpelt
                rightSpelt isOp isRead facts) _
            (after1 step =>
              let parts := step.parts
              let at16: infixLevel InfixBinary operator.text = 16 := arithmetic [fits, level, binaryAtMost op.kind isOp]
              let needs := mulNeeds operator.text at16
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
                  (highUnary right rightRead rightSpelt (arithmetic [rightFits, needs.right]))
              let tail := [(op, rightRead, right), ..links]
              let afterTail: UnaryEnds modes (Parse.loopReads [] (linkSteps tail) ++ rest) :=
                chainReads
                  (items => UnaryEnds modes [op, ..items])
                  rightRead
                  (Parse.loopReads [] (linkSteps links))
                  rest
                  (opEnds modes 17 op
                    (rightRead ++ rightAfter)
                    InfixBinary
                    parts.openOp
                    isOp
                    (Eq.trans (speltApart right rightRead rightAfter rightSpelt) apart)
                    (arithmetic [rungMulOf op.kind isMul])).unary
              let wholeTail := chainWhole all read leftRead op rightRead links right whole isRead
              let valueTail := chainValue value left right operator op rightRead links isValue isWord
              mulAccHung modes quiet left leftRead tail rest depth all value state inner wholeTail valueTail
                (arithmetic [deep])
                leftSpelt
                (Bool.andLeft free)
                {
                  lineRead = parts.lineLeft,
                  lineRest = step.lineTail,
                  openFirst = parts.openLeft,
                  bound = parts.boundLeft,
                  hung = step.hungTail,
                  deepItems = step.deepTail
                }
                afterTail
                (parts.openOp, isMul, rightReads, linked)
                (arithmetic [leftFits, needs.left]))
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
          withWitness _
            (chainStep modes quiet InfixBinary left right read leftRead op rightRead links rest state leftSpelt
                rightSpelt isOp isRead facts) _
            (after1 step =>
              let parts := step.parts
              let at14: infixLevel InfixBinary operator.text = 14 := arithmetic [level, is14]
              let needs := addNeeds operator.text at14
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
                  (arithmetic [rightFits, needs.right])
              let tail := [(op, rightRead, right), ..links]
              let afterTail: EndsAt modes 16 (Parse.loopReads [] (linkSteps tail) ++ rest) :=
                chainReads
                  (items => EndsAt modes 16 [op, ..items])
                  rightRead
                  (Parse.loopReads [] (linkSteps links))
                  rest
                  (opEnds modes 16 op
                    (rightRead ++ rightAfter)
                    InfixBinary
                    parts.openOp
                    isOp
                    (Eq.trans (speltApart right rightRead rightAfter rightSpelt) apart)
                    (arithmetic [rungAddOf op.kind isAdd]))
              let wholeTail := chainWhole all read leftRead op rightRead links right whole isRead
              let valueTail := chainValue value left right operator op rightRead links isValue isWord
              addAccHung modes quiet left leftRead tail rest depth all value state inner wholeTail valueTail
                (arithmetic [deep])
                leftSpelt
                (Bool.andLeft free)
                {
                  lineRead = parts.lineLeft,
                  lineRest = step.lineTail,
                  openFirst = parts.openLeft,
                  bound = parts.boundLeft,
                  hung = step.hungTail,
                  deepItems = step.deepTail
                }
                afterTail
                (parts.openOp, isAdd, rightReads, linked)
                (arithmetic [leftFits, needs.left]))
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
          withWitness _
            (infixStep modes quiet InfixBinary left right read leftRead op rightRead rest state leftSpelt rightSpelt
                isOp isRead facts) _
            (after1 step =>
              let parts := step.parts
              let at12: infixLevel InfixBinary operator.text = 12 := arithmetic [level, is12]
              let needs := appendNeeds operator.text at12
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
                  (arithmetic [rightFits, needs.right])
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
                    lineRest = step.lineOpTail,
                    openFirst = parts.openLeft,
                    bound = parts.boundLeft,
                    hung = step.hungLeft,
                    deepItems = step.deepLeft
                  }
                  (opEnds modes 14 op
                    (rightRead ++ rest)
                    InfixBinary
                    parts.openOp
                    isOp
                    (Eq.trans (speltApart right rightRead rest rightSpelt) apart)
                    (arithmetic [rungAppendOf op.kind isAppend]))
                  (arithmetic [leftFits, needs.left])
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
                rightReads)
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
          withWitness _
            (infixStep modes quiet InfixBinary left right read leftRead op rightRead rest state leftSpelt rightSpelt
                isOp isRead facts) _
            (after1 step =>
              let parts := step.parts
              let at6: infixLevel InfixBinary operator.text = 6 := arithmetic [level, is6]
              let needs := cmpNeeds operator.text at6
              let kinds := cmpOf op.kind isOp is6
              let leftEnds: EndsAt modes 12 [op, ..rightRead ++ rest] :=
                opEnds modes 12 op
                  (rightRead ++ rest)
                  InfixBinary
                  parts.openOp
                  isOp
                  (Eq.trans (speltApart right rightRead rest rightSpelt) apart)
                  (arithmetic [rungCmpOf op.kind kinds.left])
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
                    lineRest = step.lineOpTail,
                    openFirst = parts.openLeft,
                    bound = parts.boundLeft,
                    hung = step.hungLeft,
                    deepItems = step.deepLeft
                  }
                  leftEnds
                  (aboveCmp left leftRead leftSpelt (arithmetic [leftFits, needs.left]))
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
                  (aboveCmp right rightRead rightSpelt (arithmetic [rightFits, needs.right]))
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
                kinds.right,
                kinds.left,
                cmpNoIf modes right rightRead rest rightSpelt parts.openRight,
                (ends.noRange, ends.noPipe, rightReads),
                ends.noCmp (arithmetic [])
              ))
    | Infix InfixArrow _ _ _, _, fits => Void.impossible (arithmetic [fits])
    | Infix _ _ _ _, (_, _, _, _, never, _), _ => (Bool.falseNotTrue never).impossible
    | other, spelt, _ =>
      cmpAloneHung modes quiet other read rest depth state inner deep spelt free facts ends
        (arithmetic [unaryLevel other read spelt byComputing])
