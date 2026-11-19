--| The frame (H3 of SW-4121's plan): the line rule's state after a spelt expression's leaves is the state its first
--| leaf entered, every bracket inside closed and no `->` left hanging.

namespace Syntax.ReadBackHungFrame
import Std (Bool, List, Nat, Option, Parse, Void)
import Syntax (..)
import Fmt (..)
import Syntax.ReadBackProofs (..)
import Syntax.ReadBackRuns (..)
import Syntax.ReadBackLine (..)
import Syntax.ReadBackHung (..)
import Syntax.ReadBackHungFrameLemmas (..)

--| The frame over a read: the state after the leaves of a spelt expression is the one its first leaf enters, from
--| any state. By induction on the expression: a bracket's first leaf opens it, the items keep the state inside it
--| (`Within`) with the commas starting each next item, and the closer leaves the state that first leaf entered; a call,
--| a sign and an operator are stepped over from the state the first leaf entered, which leaves it as it is.
theorem speltEnters ∀ (expr: Expr) (read: List Item)
    (spelt: Spelt expr read) (state next: HangState)
    (after: state.after (leavesOf read) = Some next):
    next = state.enters read :=
  match expr, spelt with
    | Atom kind word, (item, isRead, isKind, _, wordOk) =>
      rewrite isRead at after then
        let flat := wordIsFlat item.kind (rewrite isKind then wordOk)
        let noArrow := wordIsNoArrow item.kind (rewrite isKind then wordOk)
        rewrite isRead then flatStep state next item.leaf flat noArrow (afterOne state next item.leaf after)
    | Paren _ inner _, (first, inside, last, isRead, isOpen, _, isClose, _, innerSpelt) =>
      rewrite isRead at after then
        let opener: first.kind.isOpener = True := rewrite isOpen
        let closer: last.kind.isCloser = True := rewrite isClose
        let (s0, openStepped, afterInner) := afterCons state next first.leaf (leavesOf (inside ++ [last])) after
        let (m, insideAfter, lastAfter) :=
          afterSplit s0 next
            (leavesOf inside)
            [last.leaf]
            (rewrite leavesOfAppend inside [last] at afterInner then afterInner)
        let isEnters := speltEnters inner inside innerSpelt s0 m insideAfter
        let within0 := openWithin state s0 first.leaf opener openStepped
        let withinM: Within m (state.entered first.leaf) := rewrite isEnters then entersWithin s0 _ inside within0
        rewrite isRead then
          closeBracket state m next first.leaf last.leaf closer withinM (afterOne m next last.leaf lastAfter)
    | Tuple _ [one, two, ..others] _ _, (first, read1, separator, read2, steps, last, isRead, _, isOpen, _, isComma,
        isClose, _, oneSpelt, twoSpelt, stepsSpelt) =>
      rewrite isRead at after then
        let opener: first.kind.isOpener = True := rewrite isOpen
        let closer: last.kind.isCloser = True := rewrite isClose
        let isCommaKind: (separator.kind == Comma) = True := rewrite isComma
        let (s0, openStepped, afterInner) :=
          afterCons state next first.leaf
            (leavesOf (read1 ++ ([separator, ..read2] ++ (commaReads steps ++ [last]))))
            after
        let within0 := openWithin state s0 first.leaf opener openStepped
        let (m1, oneAfter, afterRest) :=
          afterSplit s0 next
            (leavesOf read1)
            (leavesOf ([separator, ..read2] ++ (commaReads steps ++ [last])))
            (rewrite leavesOfAppend read1 ([separator, ..read2] ++ (commaReads steps ++ [last])) at afterInner then
              afterInner)
        let within1: Within m1 (state.entered first.leaf) :=
          rewrite speltEnters one read1 oneSpelt s0 m1 oneAfter then entersWithin s0 _ read1 within0
        let (s1, commaStepped, afterSecond) :=
          afterCons m1 next separator.leaf (leavesOf (read2 ++ (commaReads steps ++ [last]))) afterRest
        let withinS1 := commaWithin m1 s1 _ separator.leaf within1 isCommaKind commaStepped
        let (m2, twoAfter, afterSteps) :=
          afterSplit s1 next
            (leavesOf read2)
            (leavesOf (commaReads steps ++ [last]))
            (rewrite leavesOfAppend read2 (commaReads steps ++ [last]) at afterSecond then afterSecond)
        let within2: Within m2 (state.entered first.leaf) :=
          rewrite speltEnters two read2 twoSpelt s1 m2 twoAfter then entersWithin s1 _ read2 withinS1
        let (m3, stepsAfter, lastAfter) :=
          afterSplit m2 next
            (leavesOf (commaReads steps))
            [last.leaf]
            (rewrite leavesOfAppend (commaReads steps) [last] at afterSteps then afterSteps)
        let within3 := stepsWithin others steps stepsSpelt m2 m3 _ within2 stepsAfter
        rewrite isRead then
          closeBracket state m3 next first.leaf last.leaf closer within3 (afterOne m3 next last.leaf lastAfter)
    | ListOf _ [] _ _, (first, last, isRead, _, isOpen, _, isClose, _) =>
      rewrite isRead at after then
        let opener: first.kind.isOpener = True := rewrite isOpen
        let closer: last.kind.isCloser = True := rewrite isClose
        let (s0, openStepped, afterLast) := afterCons state next first.leaf [last.leaf] after
        let within0 := openWithin state s0 first.leaf opener openStepped
        rewrite isRead then
          closeBracket state s0 next first.leaf last.leaf closer within0 (afterOne s0 next last.leaf afterLast)
    | ListOf _ [one, ..others] _ _, (first, read1, steps, last, isRead, _, isOpen, _, isClose, _, oneSpelt,
        stepsSpelt) =>
      rewrite isRead at after then
        let opener: first.kind.isOpener = True := rewrite isOpen
        let closer: last.kind.isCloser = True := rewrite isClose
        let (s0, openStepped, afterInner) :=
          afterCons state next first.leaf (leavesOf (read1 ++ (commaReads steps ++ [last]))) after
        let within0 := openWithin state s0 first.leaf opener openStepped
        let (m1, oneAfter, afterRest) :=
          afterSplit s0 next
            (leavesOf read1)
            (leavesOf (commaReads steps ++ [last]))
            (rewrite leavesOfAppend read1 (commaReads steps ++ [last]) at afterInner then afterInner)
        let within1: Within m1 (state.entered first.leaf) :=
          rewrite speltEnters one read1 oneSpelt s0 m1 oneAfter then entersWithin s0 _ read1 within0
        let (m2, stepsAfter, lastAfter) :=
          afterSplit m1 next
            (leavesOf (commaReads steps))
            [last.leaf]
            (rewrite leavesOfAppend (commaReads steps) [last] at afterRest then afterRest)
        let within2 := stepsWithin others steps stepsSpelt m1 m2 _ within1 stepsAfter
        rewrite isRead then
          closeBracket state m2 next first.leaf last.leaf closer within2 (afterOne m2 next last.leaf lastAfter)
    | App head [argument, ..more], (headRead, argRead, steps, isRead, _, _, headSpelt, argSpelt, argsSpelt) =>
      rewrite isRead at after then
        let (h, hmore, isHead, _) := speltStarts head headRead headSpelt
        let (m1, headAfter, afterRest) :=
          afterSplit state next
            (leavesOf headRead)
            (leavesOf (argRead ++ Parse.loopReads [] steps))
            (rewrite leavesOfAppend headRead (argRead ++ Parse.loopReads [] steps) at after then after)
        let isFirst: m1 = state.entered h.leaf := rewrite speltEnters head headRead headSpelt state m1 headAfter, isHead
        let (m2, argAfter, afterSteps) :=
          afterSplit m1 next
            (leavesOf argRead)
            (leavesOf (Parse.loopReads [] steps))
            (rewrite leavesOfAppend argRead (Parse.loopReads [] steps) at afterRest then afterRest)
        let isSecond: m2 = state.entered h.leaf :=
          rewrite speltEnters argument argRead argSpelt m1 m2 argAfter, isFirst then entersSame state h.leaf argRead
        let final := argsEnters more steps argsSpelt state next h.leaf (rewrite isSecond at afterSteps then afterSteps)
        rewrite isRead, isHead then final
    | Prefix _ operand, (sign, tail, isRead, signed, _, _, _, operandSpelt) =>
      rewrite isRead at after then
        let (s1, signStepped, afterOperand) := afterCons state next sign.leaf (leavesOf tail) after
        let isSign: s1 = state.entered sign.leaf :=
          flatStep state s1 sign.leaf (signIsFlat sign.kind signed) (signIsNoArrow sign.kind signed) signStepped
        let isOperand := speltEnters operand tail operandSpelt s1 next afterOperand
        rewrite isRead then (rewrite isOperand, isSign then entersSame state sign.leaf tail)
    | Infix kind left _ right, (leftRead, op, rightRead, isRead, isOp, _, _, _, _, _, leftSpelt, rightSpelt) =>
      rewrite isRead at after then
        let (f, fmore, isLeft, _) := speltStarts left leftRead leftSpelt
        let (r, rmore, isRight, _) := speltStarts right rightRead rightSpelt
        let (m1, leftAfter, afterRest) :=
          afterSplit state next
            (leavesOf leftRead)
            (leavesOf [op, ..rightRead])
            (rewrite leavesOfAppend leftRead [op, ..rightRead] at after then after)
        let isFirst: m1 = state.entered f.leaf := rewrite speltEnters left leftRead leftSpelt state m1 leftAfter, isLeft
        let (m2, opStepped, rightAfter) := afterCons m1 next op.leaf (leavesOf rightRead) afterRest
        let isRight2 := speltEnters right rightRead rightSpelt m2 next rightAfter
        let flat := infixIsFlat kind op.kind isOp
        let closed := afterOperator state m2 f.leaf op.leaf r.leaf flat (rewrite isFirst at opStepped then opStepped)
        rewrite isRead, isLeft then (rewrite isRight2, isRight then closed)
    | _, never => Void.impossible never

--| The commas and items after a bracket's first (or first two) items keep the state inside the bracket.
theorem stepsWithin ∀ (exprs: List Expr) (steps: List (Item, List Item, Expr))
    (spelt: SpeltSteps exprs steps) (state next entered: HangState)
    (within: Within state entered)
    (after: state.after (leavesOf (commaReads steps)) = Some next):
    Within next entered :=
  match exprs, spelt with
    | [], isEmpty =>
      let same := afterNil state next (rewrite isEmpty at after then after)
      rewrite same then within
    | [expr, ..rest], (comma, read, later, isSteps, isComma, exprSpelt, restSpelt) =>
      rewrite isSteps at after then
        let (s1, stepped, afterRest) := afterCons state next comma.leaf (leavesOf (read ++ commaReads later)) after
        let isCommaKind: (comma.kind == Comma) = True := rewrite isComma
        let withinS1 := commaWithin state s1 entered comma.leaf within isCommaKind stepped
        let (m, readAfter, laterAfter) :=
          afterSplit s1 next
            (leavesOf read)
            (leavesOf (commaReads later))
            (rewrite leavesOfAppend read (commaReads later) at afterRest then afterRest)
        let isEnters := speltEnters expr read exprSpelt s1 m readAfter
        let withinM: Within m entered := rewrite isEnters then entersWithin s1 entered read withinS1
        stepsWithin rest later restSpelt m next entered withinM laterAfter

--| A call's arguments after the first leave the state the call's first leaf entered.
theorem argsEnters ∀ (exprs: List Expr) (steps: List (List Item, Expr))
    (spelt: SpeltArgs exprs steps)
    (state next: HangState) (first: Leaf)
    (after: (state.entered first).after (leavesOf (Parse.loopReads [] steps)) = Some next):
    next = state.entered first :=
  match exprs, spelt with
    | [], isEmpty => afterNil (state.entered first) next (rewrite isEmpty at after then after)
    | [argument, ..rest], (read, later, isSteps, _, argSpelt, restSpelt) =>
      rewrite isSteps at after then
        let (m, readAfter, laterAfter) :=
          afterSplit
            (state.entered first)
            next
            (leavesOf read)
            (leavesOf (Parse.loopReads [] later))
            (rewrite leavesOfAppend read (Parse.loopReads [] later) at after then after)
        let isEnters := speltEnters argument read argSpelt (state.entered first) m readAfter
        let same: m = state.entered first := rewrite isEnters then entersSame state first read
        argsEnters rest later restSpelt state next first (rewrite same at laterAfter then laterAfter)

--| The frame: the line rule's state after a spelt expression's leaves is the state its first leaf entered.
theorem speltHangs ∀ (expr: Expr) (first: Item) (more: List Item) (state next: HangState)
    (spelt: Spelt expr [first, ..more])
    (after: state.after (leavesOf [first, ..more]) = Some next):
    next = state.entered first.leaf :=
  speltEnters expr [first, ..more] spelt state next after

--| `speltHangs`' hypotheses hold: `(- -- c⏎  1)` read from a value's start leaves the state its `(` entered.
theorem speltHangsExample: ({ blocks = [], top = None, start = True, glue = False }).entered (commentAt 5).leaf
      = ({ blocks = [], top = None, start = True, glue = False }).entered (commentAt 5).leaf :=
  speltHangs commentValue
    (commentAt 5)
    [commentAt 6, commentAt 7, commentAt 8]
    { blocks = [], top = None, start = True, glue = False }
    (({ blocks = [], top = None, start = True, glue = False }).entered (commentAt 5).leaf)
    commentSpeltExample
    byComputing
