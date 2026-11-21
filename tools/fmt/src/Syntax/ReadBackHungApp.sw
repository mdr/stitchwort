--| Calls and signs on any lines (H6 of SW-4121's plan): a sign's argument, a call's arguments, its head, the call and
--| the unary level, read from the line rule's state, as in `Syntax.ReadBackHungAtoms`.

namespace Syntax.ReadBackHungApp
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
import Syntax.ReadBackHungAtoms (..)
import Syntax.ReadBackHungFrame (speltEnters)
import Syntax.ReadBackHungFrameLemmas (leavesOfAppend)
import Syntax.ReadBackHungAtomsLemmas (hungSplit, leadHung, speltHung, deepRest)
import Syntax.ReadBackHungAppLemmas (..)

--| A sign glued to an atom, as a call's argument. The state is the line rule's before the sign, which the modes'
--| limit is within: a sign that starts a line is then right of the limit, which the state the sign enters wouldn't
--| say where the sign starts an item.
--|
--| Proof idea: the line facts by `leadHung`: the sign and the operand's first item stop no reading,
--| the bound carrying past the sign, and `atomHung` reads the operand from the state the sign left.
theorem signArgHung ∀ (modes: Modes)
    (quiet: Quiet modes)
    (operator: Word) (operand: Expr) (read later: List Item) (depth: Nat) (state: HangState)
    (inner: FullHungBelow depth)
    (deep: (Prefix operator operand).nest <= depth)
    (spelt: Spelt (Prefix operator operand) read)
    (atomic: operand.primary = True)
    (glue: argumentGlue read = True)
    (free: operand.autoPlaced False = True)
    (lineRead: lineAll read = True)
    (lineLater: lineAll later = True)
    (bound: bounds modes state = True)
    (hung: hangsFrom state (leavesOf (read ++ later)) = True)
    (deepItems: deepAll (read ++ later) = True)
    (after: ∀ (kind: Tok) => AtomEnds modes False kind later):
    AtomReads (TreeN depth) modes False read later (Prefix operator operand) :=
  let (sign, more, isRead, isSign, isWord, numeral, _, operandSpelt) := spelt
  let shape: read ++ later = [sign, ..more ++ later] := rewrite isRead
  let hungItems: hangsFrom state (leavesOf [sign, ..more ++ later]) = True := rewrite <- shape then hung
  let deepSign: deepAll [sign, ..more ++ later] = True := rewrite <- shape then deepItems
  let deepMore: deepAll (more ++ later) = True := Bool.andRight deepSign
  let (openSign, _, (s1, s1Bound, hungMore)) :=
    leadHung modes state sign (more ++ later) quiet (signLead sign.kind isSign) bound hungItems
  let (next, others, isMore, nextStarts) := speltPlainStarts operand more operandSpelt (atomicUnsigned operand atomic)
  let hungNext: hangsFrom s1 (leavesOf ([next, ..others] ++ later)) = True := rewrite <- isMore then hungMore
  let (openNext, _, _) :=
    leadHung modes s1 next (others ++ later) quiet (startLead next.kind nextStarts) s1Bound hungNext
  let (operandBound, _) := speltHung modes operand more later s1 operandSpelt s1Bound hungMore
  let lineItems: lineAll [sign, ..more] = True := rewrite <- isRead then lineRead
  let lineMore: lineAll more = True := Bool.andRight lineItems
  let glueMore: argumentGlue [sign, ..more] = True :=
    Eq.trans (Eq.cong (taken => argumentGlue taken) isRead).flipped glue
  let glueNext: argumentGlue [sign, next, ..others] = True :=
    Eq.trans (Eq.cong (taken => argumentGlue [sign, ..taken]) isMore).flipped glueMore
  let glueAll: argumentGlue [sign, next, ..others ++ later] = True := glueNext
  let prefix := argumentPrefixHung sign next (others ++ later) isSign glueAll (startOpensAtom next.kind nextStarts)
  let atMore: argumentPrefix [sign, ..more ++ later] = True := rewrite isMore then prefix
  let numeralAfter: negativeNumeral [sign, ..more ++ later] = negativeNumeral [sign, ..more] := rewrite isMore
  let openMore: openHead modes more = True := rewrite isMore then openHeadOf modes next others openNext
  match depth, deep, inner with
    | Zero, deep, _ => Void.impossible (arithmetic [deep])
    | Succ below, deep, inner =>
      let base: BaseReads (TreeN (Succ below)) modes sign more later (Prefix operator operand) :=
        match negative: negativeNumeral [sign, ..more] with
          | False =>
            let signs: (sign.kind = Minus
              ∧ negativeNumeral [sign, ..more ++ later] = False
              ∧ argumentMinus [sign, ..more ++ later] = True)
              ∨ (sign.kind = Bang ∧ argumentBang [sign, ..more ++ later] = True) :=
              match signCases sign.kind isSign with
                | Inl isMinus => Inl (isMinus, (rewrite numeralAfter then negative), (rewrite isMinus, atMore))
                | Inr isBang => Inr (isBang, (rewrite isBang, atMore))
            Inr
              (Inr
                (Inr
                  (Inr
                    (Inr
                      (Inr (
                        operand,
                        (rewrite isWord),
                        signs,
                        atomHung modes quiet False operand more later below s1
                          (belowLess below (Succ below) (arithmetic []) inner)
                          (arithmetic [deep])
                          operandSpelt
                          atomic
                          free
                          {
                            lineRead = lineMore,
                            lineRest = lineLater,
                            openFirst = openMore,
                            bound = operandBound,
                            hung = hungMore,
                            deepItems = deepMore
                          }
                          after
                      ))))))
          | True =>
            match operand, operandSpelt, numeral negative with
              | Atom kind word, (number, isNumber, isKind, isNumberWord, _), _ =>
                let isMinus: sign.kind = Minus := negativeMinus sign more negative
                let atNumber: negativeNumeral [sign, number] = True := rewrite <- isNumber then negative
                let negNumber: negativeNumeral [sign, number, ..later] = True := atNumber
                Inr
                  (Inr
                    (Inr
                      (Inr (Inr (Inl (number, isNumber, (rewrite isWord, isKind, isNumberWord), isMinus, negNumber))))))
              | other, _, never => (Bool.falseNotTrue never).impossible
      (sign, more, isRead, openSign, after sign.kind, base)

--| One argument of a call. The state is the line rule's before the argument, which the modes' limit is within, as
--| for `signArgHung`.
theorem argumentHung ∀ (modes: Modes)
    (quiet: Quiet modes)
    (argument: Expr) (read later: List Item) (below: Nat) (state: HangState)
    (inner: FullHungBelow (Succ below))
    (deep: argument.nest <= below)
    (spelt: Spelt argument read)
    (fits: argumentFits argument read = True)
    (free: argument.autoPlaced False = True)
    (lineRead: lineAll read = True)
    (lineLater: lineAll later = True)
    (bound: bounds modes state = True)
    (hung: hangsFrom state (leavesOf (read ++ later)) = True)
    (deepItems: deepAll (read ++ later) = True)
    (after: ∀ (kind: Tok) => AtomEnds modes False kind later):
    ArgumentReads (TreeN (Succ below)) modes read later argument :=
  let (first, more, isRead, lead) := speltStarts argument read spelt
  let notDot := leadNotDot first.kind lead
  let shape: read ++ later = [first, ..more ++ later] := rewrite isRead
  let hungItems: hangsFrom state (leavesOf [first, ..more ++ later]) = True := rewrite <- shape then hung
  let (open, _, _) := leadHung modes state first (more ++ later) quiet lead bound hungItems
  let openRead: openHead modes read = True := rewrite isRead then openHeadOf modes first more open
  let (entered, _) := speltHung modes argument read later state spelt bound hung
  let innerBelow := belowLess below (Succ below) (arithmetic []) inner
  let atom: AtomReads (TreeN below) modes False read later argument := match signed: argument.signed with
    | False =>
      atomHung modes quiet False argument read later below state innerBelow deep spelt
        (signArgAtomic argument (Bool.andLeft fits) signed)
        free
        {
          lineRead = lineRead,
          lineRest = lineLater,
          openFirst = openRead,
          bound = entered,
          hung = hung,
          deepItems = deepItems
        }
        after
    | True =>
      match argument, spelt, fits, free, deep, signed with
        | Prefix operator operand, spelt, fits, free, deep, _ =>
          signArgHung modes quiet operator operand read later below state innerBelow deep spelt
            (Bool.andLeft fits)
            (Bool.andRight fits)
            free
            lineRead
            lineLater
            bound
            hung
            deepItems
            after
        | Infix _ _ _ _ | App _ _, _, fits, _, _, _ => (Bool.falseNotTrue fits).impossible
        | other, _, _, _, _, never => (Bool.falseNotTrue never).impossible
  (
    (rewrite isRead, notDot),
    Bool.andFalseRight _ _ (peekNoBrace modes 1 (read ++ later) (lineJoin read later lineRead lineLater)),
    atom
  )

--| A call's arguments after the first: `state` is the line rule's before the first of them.
--|
--| Proof idea: each argument read by `argumentHung` from the state the arguments before it left, which
--| `speltHung` gives with the bound.
theorem argsHung ∀ (modes: Modes)
    (quiet: Quiet modes)
    (exprs: List Expr) (steps: List (List Item, Expr)) (rest: List Item) (below: Nat) (state: HangState)
    (inner: FullHungBelow (Succ below))
    (deep: nestAll exprs <= below)
    (spelt: SpeltArgs exprs steps)
    (free: autoPlacedAll False exprs = True)
    (lineSteps: lineAll (Parse.loopReads [] steps) = True)
    (lineRest: lineAll rest = True)
    (bound: bounds modes state = True)
    (hung: hangsFrom state (leavesOf (Parse.loopReads [] steps ++ rest)) = True)
    (deepItems: deepAll (Parse.loopReads [] steps ++ rest) = True)
    (ends: UnaryEnds modes rest):
    ArgsReads (TreeN (Succ below)) modes steps rest :=
  match exprs, spelt, free with
    | [], isEmpty, _ => rewrite isEmpty then ends.noArgument
    | [argument, ..more], (read, later, isSteps, fits, argSpelt, moreSpelt), free =>
      let lineHere: lineAll (read ++ Parse.loopReads [] later) = True :=
        Eq.trans (Eq.cong (taken => lineAll (Parse.loopReads [] taken)) isSteps).flipped lineSteps
      let (lineRead, lineLater) := lineSplit read (Parse.loopReads [] later) lineHere
      let whole: Parse.loopReads [] steps ++ rest = read ++ (Parse.loopReads [] later ++ rest) :=
        rewrite isSteps then List.appendAssoc read (Parse.loopReads [] later) rest
      let hungHere: hangsFrom state (leavesOf (read ++ (Parse.loopReads [] later ++ rest))) = True :=
        rewrite <- whole then hung
      let deepHere: deepAll (read ++ (Parse.loopReads [] later ++ rest)) = True := rewrite <- whole then deepItems
      let deepLater := deepRest read (Parse.loopReads [] later ++ rest) deepHere
      let (first, inside, isRead, lead) := speltStarts argument read argSpelt
      let shape: read ++ (Parse.loopReads [] later ++ rest) = [first, ..inside ++ (Parse.loopReads [] later ++ rest)] :=
        rewrite isRead
      let hungFirst: hangsFrom state (leavesOf [first, ..inside ++ (Parse.loopReads [] later ++ rest)]) = True :=
        rewrite <- shape then hungHere
      let (open, _, _) :=
        leadHung modes state first (inside ++ (Parse.loopReads [] later ++ rest)) quiet lead bound hungFirst
      let (nextBound, hungNext) :=
        speltHung modes argument read (Parse.loopReads [] later ++ rest) state argSpelt bound hungHere
      let lineAfter: lineAll (Parse.loopReads [] later ++ rest) = True := lineJoin _ rest lineLater lineRest
      rewrite isSteps then
        (
          isEmpty => Bool.falseNotTrue (Eq.cong List.isEmpty (Eq.trans isRead.flipped isEmpty)),
          (rewrite isRead then
            argStartsHung modes argument first inside
              (Parse.loopReads [] later ++ rest)
              (rewrite <- isRead then argSpelt)
              (rewrite <- isRead then fits)
              open),
          argumentHung modes quiet argument read
            (Parse.loopReads [] later ++ rest)
            below
            state
            inner
            (arithmetic [deep])
            argSpelt
            fits
            (Bool.andLeft free)
            lineRead
            lineAfter
            bound
            hungHere
            deepHere
            (kind =>
              argEndsHung modes quiet False kind more later rest
                (state.enters read)
                moreSpelt
                lineAfter
                nextBound
                hungNext
                ends),
          argsHung modes quiet more later rest below
            (state.enters read)
            inner
            (arithmetic [deep])
            moreSpelt
            (Bool.andRight free)
            lineLater
            lineRest
            nextBound
            hungNext
            deepLater
            ends
        )

--| A call.
--|
--| Proof idea: the head is read by `headHung`; the line rule leaves the state the head's first leaf
--| entered (`speltEnters`), which the bound holds of, and from there the first argument by `argumentHung` and the
--| others by `argsHung`, from the state the first left (`speltHung`).
theorem appHung ∀ (modes: Modes)
    (quiet: Quiet modes)
    (head argument: Expr) (more: List Expr) (read rest: List Item) (depth: Nat) (state: HangState)
    (inner: FullHungBelow depth)
    (deep: (App head [argument, ..more]).nest <= depth)
    (spelt: Spelt (App head [argument, ..more]) read)
    (free: (App head [argument, ..more]).autoPlaced False = True)
    (facts: HungAt modes state read rest)
    (ends: UnaryEnds modes rest):
    AppReads (TreeN depth) modes read rest (App head [argument, ..more]) :=
  let (headRead, argRead, steps, isRead, headAtomic, argFits, headSpelt, argSpelt, argsSpelt) := spelt
  let tail := argRead ++ Parse.loopReads [] steps
  let (first, inside, isHead, starts) := speltStarts head headRead headSpelt
  let joined: read = [first, ..inside ++ tail] := calc read
    _ = headRead ++ tail := isRead
    _ = [first, ..inside ++ tail] := rewrite isHead
  let lines: lineAll (headRead ++ tail) = True := rewrite <- isRead then facts.lineRead
  let (lineHead, lineTail) := lineSplit headRead tail lines
  let (lineArg, lineSteps) := lineSplit argRead (Parse.loopReads [] steps) lineTail
  let openRead: openHead modes [first, ..inside ++ tail] = True := rewrite <- joined then facts.openFirst
  let open1 := openHeadStops modes first (inside ++ tail) openRead
  let notDot := leadNotDot first.kind starts
  let assocAll: read ++ rest = headRead ++ (tail ++ rest) := rewrite isRead then List.appendAssoc headRead tail rest
  let hungAll: hangsFrom state (leavesOf (headRead ++ (tail ++ rest))) = True := rewrite <- assocAll then facts.hung
  let deepAll1: deepAll (headRead ++ (tail ++ rest)) = True := rewrite <- assocAll then facts.deepItems
  let (mid, afterHead, hungTail) :=
    hungSplit state
      (leavesOf headRead)
      (leavesOf (tail ++ rest))
      (rewrite <- leavesOfAppend headRead (tail ++ rest) then hungAll)
  let isMid: mid = state.enters headRead := speltEnters head headRead headSpelt state mid afterHead
  let sameEnters: state.enters read = state.enters headRead := rewrite joined, isHead
  let headBound: bounds modes (state.enters headRead) = True := rewrite <- sameEnters then facts.bound
  let assocTail: tail ++ rest = argRead ++ (Parse.loopReads [] steps ++ rest) :=
    List.appendAssoc argRead (Parse.loopReads [] steps) rest
  let hungArg: hangsFrom (state.enters headRead) (leavesOf (argRead ++ (Parse.loopReads [] steps ++ rest))) = True :=
    rewrite <- assocTail, <- isMid then hungTail
  let deepArg: deepAll (argRead ++ (Parse.loopReads [] steps ++ rest)) = True :=
    rewrite <- assocTail then deepRest headRead (tail ++ rest) deepAll1
  let deepSteps := deepRest argRead (Parse.loopReads [] steps ++ rest) deepArg
  let (stepsBound, hungSteps) :=
    speltHung modes argument argRead
      (Parse.loopReads [] steps ++ rest)
      (state.enters headRead)
      argSpelt
      headBound
      hungArg
  let (argFirst, argMore, isArg, argLead) := speltStarts argument argRead argSpelt
  let argShape: argRead ++ (Parse.loopReads [] steps ++ rest)
    = [argFirst, ..argMore ++ (Parse.loopReads [] steps ++ rest)] :=
    rewrite isArg
  let (argOpen, _, _) :=
    leadHung modes
      (state.enters headRead)
      argFirst
      (argMore ++ (Parse.loopReads [] steps ++ rest))
      quiet
      argLead
      headBound
      (rewrite <- argShape then hungArg)
  let lineAfterArg: lineAll (Parse.loopReads [] steps ++ rest) = True := lineJoin _ rest lineSteps facts.lineRest
  let lineAfterHead: lineAll (tail ++ rest) = True := lineJoin tail rest lineTail facts.lineRest
  let argAt: Spelt argument [argFirst, ..argMore] := rewrite <- isArg then argSpelt
  let argJoin: [argFirst, ..argMore] ++ (Parse.loopReads [] steps ++ rest)
    = (argRead ++ Parse.loopReads [] steps) ++ rest :=
    rewrite isArg then (List.appendAssoc [argFirst, ..argMore] (Parse.loopReads [] steps) rest).flipped
  match depth, deep, inner with
    | Zero, deep, _ => Void.impossible (arithmetic [deep])
    | Succ below, deep, inner => Inr (
      headRead,
      argRead,
      steps,
      head,
      argument,
      isRead,
      (rewrite argsValues more steps argsSpelt),
      (rewrite joined, peekFirst modes first ((inside ++ tail) ++ rest) open1, notDot),
      headHung modes quiet head headRead
        (tail ++ rest)
        (Succ below)
        state
        inner
        (arithmetic [deep])
        headSpelt
        headAtomic
        (Bool.andLeft free)
        lineHead
        lineAfterHead
        (rewrite isHead then openHeadOf modes first inside open1)
        headBound
        hungAll
        deepAll1
        (kind =>
          rewrite <- argJoin then
            endsBeforeSpelt modes True kind argument argFirst argMore
              (Parse.loopReads [] steps ++ rest)
              argAt
              argOpen
              (Eq.trans (Eq.cong lineAll argJoin) lineAfterHead)),
      (rewrite <- argJoin then
        argStartsHung modes argument argFirst argMore
          (Parse.loopReads [] steps ++ rest)
          argAt
          (rewrite <- isArg then argFits)
          argOpen),
      argumentHung modes quiet argument argRead
        (Parse.loopReads [] steps ++ rest)
        below
        (state.enters headRead)
        inner
        (arithmetic [deep])
        argSpelt
        argFits
        (Bool.andLeft (Bool.andRight free))
        lineArg
        lineAfterArg
        headBound
        hungArg
        deepArg
        (kind =>
          argEndsHung modes quiet False kind more steps rest
            ((state.enters headRead).enters argRead)
            argsSpelt
            lineAfterArg
            stepsBound
            hungSteps
            ends),
      argsHung modes quiet more steps rest below
        ((state.enters headRead).enters argRead)
        inner
        (arithmetic [deep])
        argsSpelt
        (Bool.andRight (Bool.andRight free))
        lineSteps
        facts.lineRest
        stepsBound
        hungSteps
        deepSteps
        ends
    )

--| A call's head: an atom or a bracket by `atomHung`, or `-` on a numeral read as one atom.
theorem headHung ∀ (modes: Modes)
    (quiet: Quiet modes)
    (head: Expr) (read later: List Item) (depth: Nat) (state: HangState)
    (inner: FullHungBelow depth)
    (deep: head.nest <= depth)
    (spelt: Spelt head read)
    (fits: headFits head read = True)
    (free: head.autoPlaced False = True)
    (lineRead: lineAll read = True)
    (lineLater: lineAll later = True)
    (openRead: openHead modes read = True)
    (bound: bounds modes (state.enters read) = True)
    (hung: hangsFrom state (leavesOf (read ++ later)) = True)
    (deepItems: deepAll (read ++ later) = True)
    (after: ∀ (kind: Tok) => AtomEnds modes True kind later):
    AtomReads (TreeN depth) modes True read later head :=
  match atomic: head.primary with
    | True =>
      atomHung modes quiet True head read later depth state inner deep spelt atomic free
        {
          lineRead = lineRead,
          lineRest = lineLater,
          openFirst = openRead,
          bound = bound,
          hung = hung,
          deepItems = deepItems
        }
        after
    | False =>
      match head, spelt, fits, atomic with
        | Prefix operator operand, (sign, more, isRead, _, isWord, numeral, _, operandSpelt), fits, _ =>
          let neg: negativeNumeral [sign, ..more] = True := rewrite <- isRead then fits
          match operand, operandSpelt, numeral neg with
            | Atom kind word, (number, isNumber, isKind, isNumberWord, _), _ =>
              let isMinus := negativeMinus sign more neg
              let atNumber: negativeNumeral [sign, number] = True := rewrite <- isNumber then neg
              let negNumber: negativeNumeral [sign, number, ..later] = True := atNumber
              let openItems: openHead modes [sign, ..more] = True := rewrite <- isRead then openRead
              (
                sign,
                more,
                isRead,
                openHeadStops modes sign more openItems,
                after sign.kind,
                Inr
                  (Inr
                    (Inr
                      (Inr (Inr (Inl (number, isNumber, (rewrite isWord, isKind, isNumberWord), isMinus, negNumber))))))
              )
            | other, _, never => (Bool.falseNotTrue never).impossible

--| A call or an atom, unsigned: a call by `appHung`, an atom or bracket alone by `atomHung`.
theorem appAnyHung ∀ (modes: Modes)
    (quiet: Quiet modes)
    (expr: Expr) (read rest: List Item) (depth: Nat) (state: HangState)
    (inner: FullHungBelow depth)
    (deep: expr.nest <= depth)
    (spelt: Spelt expr read)
    (free: expr.autoPlaced False = True)
    (facts: HungAt modes state read rest)
    (ends: UnaryEnds modes rest)
    (unsigned: expr.signed = False)
    (plain: expr.unary = True):
    AppReads (TreeN depth) modes read rest expr :=
  let alone: expr.primary = True → AppReads (TreeN depth) modes read rest expr := atomic =>
    let (item, more, isRead, starts) := speltStarts expr read spelt
    let openItems: openHead modes [item, ..more] = True := rewrite <- isRead then facts.openFirst
    let open1 := openHeadStops modes item more openItems
    let notDot := leadNotDot item.kind starts
    Inl (
      (rewrite isRead, peekFirst modes item (more ++ rest) open1, notDot),
      atomHung modes quiet True expr read rest depth state inner deep spelt atomic free facts (kind =>
        ends.atom True kind),
      ends.noArgument
    )
  match expr, spelt with
    | App head [argument, ..more], spelt =>
      appHung modes quiet head argument more read rest depth state inner deep spelt free facts ends
    | Atom _ _ | Paren _ _ _ | Tuple _ _ _ _ | ListOf _ _ _ _, _ => alone byComputing
    | Prefix _ _, _ => (Bool.falseNotTrue unsigned.flipped).impossible
    | Infix _ _ _ _, _ => (Bool.falseNotTrue plain).impossible
    | _, never => Void.impossible never

--| The unary level: a sign and its operand, or a call.
--|
--| Proof idea: a sign the parser doesn't read as a negative numeral is read with its operand by
--| `unaryHung` one level down, from the state the sign left, which the bound carries to (`pastFirst`); the operand's
--| first item stops no reading and its entered state is bounded (`leadHung`). A negative numeral is one atom, and
--| anything else is `appAnyHung`.
theorem unaryHung ∀ (modes: Modes)
    (quiet: Quiet modes)
    (expr: Expr) (read rest: List Item) (depth: Nat) (state: HangState)
    (inner: FullHungBelow depth)
    (deep: expr.nest <= depth)
    (spelt: Spelt expr read)
    (free: expr.autoPlaced False = True)
    (facts: HungAt modes state read rest)
    (ends: UnaryEnds modes rest)
    (unary: expr.unary = True):
    UnaryReads (TreeN depth) modes read rest expr :=
  match signed: expr.signed with
    | False =>
      let (item, more, isRead, starts) := speltPlainStarts expr read spelt signed
      let openItems: openHead modes [item, ..more] = True := rewrite <- isRead then facts.openFirst
      let lineItems: lineAll [item, ..more] = True := rewrite <- isRead then facts.lineRead
      let (_, notMatch, unsigned) := startFacts item.kind starts
      Inr (
        item,
        more,
        isRead,
        openHeadStops modes item more openItems,
        notMatch,
        noBarLine modes item (more ++ rest) (lineJoin more rest (Bool.andRight lineItems) facts.lineRest),
        Inl unsigned,
        appAnyHung modes quiet expr read rest depth state inner deep spelt free facts ends signed unary
      )
    | True =>
      match expr, spelt, signed, depth, deep, inner with
        | Prefix _ _, _, _, Zero, deep, _ => Void.impossible (arithmetic [deep])
        | Prefix operator operand, (sign, more, isRead, isSign, isWord, numeral, operandUnary, operandSpelt), _, Succ
              below, deep, inner =>
          let openItems: openHead modes [sign, ..more] = True := rewrite <- isRead then facts.openFirst
          let openSign := openHeadStops modes sign more openItems
          let lineItems: lineAll [sign, ..more] = True := rewrite <- isRead then facts.lineRead
          let lineMore: lineAll more = True := Bool.andRight lineItems
          let shape: read ++ rest = [sign, ..more ++ rest] := rewrite isRead
          let hungItems: hangsFrom state (leavesOf [sign, ..more ++ rest]) = True := rewrite <- shape then facts.hung
          let deepSign: deepAll [sign, ..more ++ rest] = True := rewrite <- shape then facts.deepItems
          let deepMore: deepAll (more ++ rest) = True := Bool.andRight deepSign
          let boundNow := facts.bound
          let signBound: bounds modes (state.entered sign.leaf) = True := rewrite isRead at boundNow then boundNow
          let (s1, s1Bound, hungMore) :=
            pastFirst modes state sign (more ++ rest) (signLead sign.kind isSign) signBound hungItems
          let (first, others, isMore, lead) := speltStarts operand more operandSpelt
          let hungFirst: hangsFrom s1 (leavesOf ([first, ..others] ++ rest)) = True := rewrite <- isMore then hungMore
          let (openOperand, enteredOperand, _) := leadHung modes s1 first (others ++ rest) quiet lead s1Bound hungFirst
          let openMore: openHead modes more = True := rewrite isMore then openHeadOf modes first others openOperand
          let boundMore: bounds modes (s1.enters more) = True := rewrite isMore then enteredOperand
          let noBar := noBarLine modes sign (more ++ rest) (lineJoin more rest lineMore facts.lineRest)
          let numeralAfter: negativeNumeral [sign, ..more ++ rest] = negativeNumeral [sign, ..more] := rewrite isMore
          match negative: negativeNumeral [sign, ..more] with
            | False => Inl (
              sign,
              more,
              operand,
              isRead,
              (rewrite isWord),
              openSign,
              signOr sign.kind isSign,
              noBar,
              (rewrite numeralAfter then Bool.andFalseRight _ _ negative),
              unaryHung modes quiet operand more rest below s1
                (belowLess below (Succ below) (arithmetic []) inner)
                (arithmetic [deep])
                operandSpelt
                free
                {
                  lineRead = lineMore,
                  lineRest = facts.lineRest,
                  openFirst = openMore,
                  bound = boundMore,
                  hung = hungMore,
                  deepItems = deepMore
                }
                ends
                operandUnary
            )
            | True =>
              match operand, operandSpelt, numeral negative with
                | Atom kind word, (number, isNumber, isKind, isNumberWord, _), _ =>
                  let isMinus: sign.kind = Minus := negativeMinus sign more negative
                  let atNumber: negativeNumeral [sign, number] = True := rewrite <- isNumber then negative
                  let negNumber: negativeNumeral [sign, number, ..rest] = True := atNumber
                  let atomReads: AtomReads
                    (TreeN (Succ below))
                    modes
                    True
                    [sign, ..more]
                    rest
                    (Prefix operator (Atom kind word)) :=
                    (
                      sign,
                      more,
                      byComputing,
                      openSign,
                      ends.atom True sign.kind,
                      Inr
                        (Inr
                          (Inr
                            (Inr
                              (Inr
                                (Inl (number, isNumber, (rewrite isWord, isKind, isNumberWord), isMinus, negNumber))))))
                    )
                  rewrite isRead then
                    Inr (
                      sign,
                      more,
                      byComputing,
                      openSign,
                      (rewrite isMinus),
                      noBar,
                      Inr ((rewrite isMinus), (rewrite isNumber then negNumber)),
                      Inl ((rewrite peekFirst modes sign (more ++ rest) openSign, isMinus), atomReads, ends.noArgument)
                    )
                | other, _, never => (Bool.falseNotTrue never).impossible
        | App head [argument, ..arguments], spelt, signed, depth, deep, inner =>
          let (headRead, argRead, steps, isRead, fits, _, headSpelt, _, _) := spelt
          match head, headSpelt, fits, signed with
            | Prefix _ operand, (sign, more, isHead, _, _, numeral, _, operandSpelt), fits, _ =>
              let neg: negativeNumeral [sign, ..more] = True := rewrite <- isHead then fits
              match operand, operandSpelt, numeral neg with
                | Atom _ _, (number, isNumber, _, _, _), _ =>
                  let isMinus := negativeMinus sign more neg
                  let tail := argRead ++ Parse.loopReads [] steps
                  let joined: read = [sign, number, ..tail] := rewrite isRead, isHead, isNumber
                  let atNumber: negativeNumeral [sign, number] = True := rewrite <- isNumber then neg
                  let negAll: negativeNumeral [sign, number, ..tail ++ rest] = True := atNumber
                  let openItems: openHead modes [sign, number, ..tail] = True := rewrite <- joined then facts.openFirst
                  let openSign := openHeadStops modes sign [number, ..tail] openItems
                  let lineItems: lineAll [sign, number, ..tail] = True := rewrite <- joined then facts.lineRead
                  let noBar :=
                    noBarLine modes sign
                      ([number, ..tail] ++ rest)
                      (lineJoin [number, ..tail] rest (Bool.andRight lineItems) facts.lineRest)
                  let call :=
                    appHung modes quiet head argument arguments read rest depth state inner deep spelt free facts ends
                  rewrite joined at call then
                    rewrite joined then
                      Inr (
                        sign,
                        [number, ..tail],
                        byComputing,
                        openSign,
                        (rewrite isMinus),
                        noBar,
                        Inr ((rewrite isMinus), negAll),
                        call
                      )
                | other, _, never => (Bool.falseNotTrue never).impossible
            | App _ _ | Infix _ _ _ _, _, never, _ => (Bool.falseNotTrue never).impossible
            | other, _, _, never => (Bool.falseNotTrue never).impossible
        | App _ [], never, _, _, _, _ => Void.impossible never
        | Infix _ _ _ _, _, _, _, _, _ => (Bool.falseNotTrue unary).impossible
        | other, _, never, _, _, _ => (Bool.falseNotTrue never).impossible
