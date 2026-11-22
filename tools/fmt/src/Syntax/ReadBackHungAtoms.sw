--| Atoms and brackets on any lines (H5 of SW-4121's plan): an atom, a tuple's and a list's items, and a bracket's
--| first item. Each takes the state before the first item (`state`), the modes' limit bounded against the state that
--| item enters (`bound`), the line rule over the items and what follows (`hung`), every closer and comma inside a
--| bracket (`deepItems`), and `fullHung` below the depth (`inner`) for the expressions inside the brackets.
--| `openStepsHung` takes the items' spelling instead of their line facts: what keeps a comma or closer from stopping
--| a reading is that it is one, inside a bracket.

namespace Syntax.ReadBackHungAtoms
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
import Syntax.ReadBackHungBounds (hungStops, boundsCong)
import Syntax.ReadBackHungFrameLemmas (hangOpenStep)
import Syntax.ReadBackHungAtomsLemmas (..)

--| A spelt expression is what `atom` reads, on any lines the line rule allows.
--|
--| Proof idea: by the atom's kind. A bracket's opener puts the line rule at the start of its first item, with the
--| column in force the one the opener entered, which the modes' limit is within (`hangOpenStep`); each item is read by
--| `fullHung` from the start of an item, a comma restarting it (`commaNext`), and the state an item leaves gives the
--| next item's start back (`entersNext`). Commas and the closer never stop a reading, being inside the bracket
--| (`deepStops`); the peeks at an item's first leaves see them unstopped as the line rule steps over them
--| (`speltOutsideHung`, `peekTwoHung`).
theorem atomHung ∀ (modes: Modes)
    (quiet: QuietModes modes)
    (head: Bool) (expr: Expr) (read rest: List Item) (depth: Nat) (state: HangState)
    (inner: FullHungBelow depth)
    (deep: expr.nest <= depth)
    (spelt: Spelt expr read)
    (atomic: expr.primary = True)
    (free: expr.autoPlaced False = True)
    (facts: HungAt modes state read rest)
    (after: ∀ (kind: Tok) => AtomEnds modes head kind rest):
    AtomReads (TreeN depth) modes head read rest expr :=
  let innerModes := modes.inBrackets
  let innerQuiet := quietBrackets modes quiet
  match expr, spelt with
    | Atom kind word, (item, isRead, isKind, isWord, word) =>
      let openItem: openHead modes [item] = True := rewrite <- isRead then facts.openFirst
      rewrite isRead then
        (
          item,
          [],
          byComputing,
          openHeadStops modes item [] openItem,
          after item.kind,
          Inl (byComputing, (rewrite isKind, isWord), rewrite isKind then (wordPlain kind word).left)
        )
    | Paren open body close, (first, inside, last, isRead, isOpen, isOpenWord, isClose, isCloseWord, bodySpelt) =>
      match depth, deep with
        | Zero, deep => Void.impossible (arithmetic [deep])
        | Succ below, deep =>
          let lineItems: lineAll [first, ..inside ++ [last]] = True := rewrite <- isRead then facts.lineRead
          let openItems: openHead modes [first, ..inside ++ [last]] = True := rewrite <- isRead then facts.openFirst
          let open1 := openHeadStops modes first (inside ++ [last]) openItems
          let (lineInside, lineLast) := lineSplit inside [last] (Bool.andRight lineItems)
          let assoc: (inside ++ [last]) ++ rest = inside ++ [last, ..rest] := List.appendAssoc inside [last] rest
          let shape: read ++ rest = [first, ..inside ++ [last, ..rest]] := rewrite isRead, assoc
          let hungItems: hangsFrom state (leavesOf [first, ..inside ++ [last, ..rest]]) = True :=
            rewrite <- shape then facts.hung
          let deepItems1: deepAll [first, ..inside ++ [last, ..rest]] = True := rewrite <- shape then facts.deepItems
          let deepBody: deepAll (inside ++ [last, ..rest]) = True := Bool.andRight deepItems1
          let deepLast := deepHead last rest (deepRest inside [last, ..rest] deepBody)
          let (s1, steppedOpen, hungBody) := hungStep state first.leaf (leavesOf (inside ++ [last, ..rest])) hungItems
          let isS1 := hangOpenStep state s1 first.leaf (rewrite isOpen) steppedOpen
          let boundNow := facts.bound
          let enteredBound: bounds modes (state.entered first.leaf) = True := rewrite isRead at boundNow then boundNow
          let s1Bound: bounds modes s1 = True :=
            boundsCong modes s1 (state.entered first.leaf) (rewrite isS1) enteredBound
          let lastOpen := deepStops modes last quiet deepLast (rewrite isClose)
          let bodyTree: TreeN (Succ below) { modes = innerModes, level = LevelFull } inside [last, ..rest] body :=
            inner below
              (arithmetic [])
              innerModes
              body
              inside
              [last, ..rest]
              s1
              innerQuiet
              (arithmetic [deep])
              bodySpelt
              free
              lineInside
              (lineJoin [last] rest lineLast facts.lineRest)
              (Inl (rewrite isS1))
              s1Bound
              hungBody
              deepBody
              (rewrite isClose)
          let plain: ParenPlain modes [first, ..(inside ++ [last]) ++ rest] := {
            notOutside = rewrite assoc then
              speltOutsideHung modes quiet first body inside
                [last, ..rest]
                s1
                bodySpelt
                open1
                s1Bound
                hungBody
                deepBody
                (openHeadOf modes last rest lastOpen)
                (rewrite isClose),
            noRight = rewrite assoc then
              rightClosed first inside last rest
                (groupInsideReverse body inside bodySpelt LParen [] [] [last, ..rest])
                (speltLast body inside bodySpelt [])
                isClose
          }
          rewrite isRead then
            (
              first,
              inside ++ [last],
              byComputing,
              open1,
              after first.kind,
              Inr
                (Inl (
                  inside,
                  last,
                  body,
                  byComputing,
                  (rewrite isOpenWord, isCloseWord),
                  isOpen,
                  plain,
                  bodyTree,
                  deepStops innerModes last innerQuiet deepLast (rewrite isClose),
                  isClose
                ))
            )
    | Tuple open [one, two, ..others] comma close, (first, read1, separator, read2, steps, last, isRead, isBare, isOpen,
        isOpenWord, isComma, isClose, isCloseWord, oneSpelt, twoSpelt, stepsSpelt) =>
      match depth, deep with
        | Zero, deep => Void.impossible (arithmetic [deep])
        | Succ below, deep =>
          let elements := [separator, ..read2] ++ (commaReads steps ++ [last])
          let lineItems: lineAll [first, ..read1 ++ elements] = True := rewrite <- isRead then facts.lineRead
          let openItems: openHead modes [first, ..read1 ++ elements] = True := rewrite <- isRead then facts.openFirst
          let open1 := openHeadStops modes first (read1 ++ elements) openItems
          let (line1, lineElements) := lineSplit read1 elements (Bool.andRight lineItems)
          let (line2, lineSteps) := lineSplit read2 (commaReads steps ++ [last]) (Bool.andRight lineElements)
          let (lineCommas, lineLast) := lineSplit (commaReads steps) [last] lineSteps
          let assoc: (read1 ++ elements) ++ rest = read1 ++ (elements ++ rest) := List.appendAssoc read1 elements rest
          let shape: read ++ rest = [first, ..read1 ++ (elements ++ rest)] := rewrite isRead, assoc
          let hungItems: hangsFrom state (leavesOf [first, ..read1 ++ (elements ++ rest)]) = True :=
            rewrite <- shape then facts.hung
          let deepItems1: deepAll [first, ..read1 ++ (elements ++ rest)] = True := rewrite <- shape then facts.deepItems
          let deep1: deepAll (read1 ++ (elements ++ rest)) = True := Bool.andRight deepItems1
          let deepElements: deepAll (elements ++ rest) = True := deepRest read1 (elements ++ rest) deep1
          let deepSeparator := deepHead separator _ deepElements
          let twoAssoc: (read2 ++ (commaReads steps ++ [last])) ++ rest
            = read2 ++ ((commaReads steps ++ [last]) ++ rest) :=
            List.appendAssoc read2 (commaReads steps ++ [last]) rest
          let deep2: deepAll (read2 ++ ((commaReads steps ++ [last]) ++ rest)) = True :=
            rewrite <- twoAssoc then Bool.andRight deepElements
          let stepsAssoc: (commaReads steps ++ [last]) ++ rest = commaReads steps ++ [last, ..rest] :=
            List.appendAssoc (commaReads steps) [last] rest
          let deepSteps: deepAll (commaReads steps ++ [last, ..rest]) = True :=
            rewrite <- stepsAssoc then deepRest read2 _ deep2
          let deepLast := deepHead last rest (deepRest (commaReads steps) [last, ..rest] deepSteps)
          let (s1, steppedOpen, hung1) := hungStep state first.leaf (leavesOf (read1 ++ (elements ++ rest))) hungItems
          let isS1 := hangOpenStep state s1 first.leaf (rewrite isOpen) steppedOpen
          let boundNow := facts.bound
          let enteredBound: bounds modes (state.entered first.leaf) = True := rewrite isRead at boundNow then boundNow
          let s1Bound: bounds modes s1 = True :=
            boundsCong modes s1 (state.entered first.leaf) (rewrite isS1) enteredBound
          let (_, hungAfterOne) := speltHung innerModes one read1 (elements ++ rest) s1 oneSpelt s1Bound hung1
          let t1 := s1.enters read1
          let (s2, steppedSeparator, hung2) :=
            hungStep t1 separator.leaf (leavesOf ((read2 ++ (commaReads steps ++ [last])) ++ rest)) hungAfterOne
          let isS2 := commaNext t1 s2 separator.leaf (rewrite isComma) steppedSeparator
          let nextBound: bounds innerModes t1.nextItem = True :=
            rewrite entersNextIn one read1 s1 None (state.entered first.leaf).blocks (rewrite isS1) oneSpelt then
              boundsCong innerModes s1.nextItem (state.entered first.leaf) (rewrite isS1) enteredBound
          let s2Bound: bounds innerModes s2 = True := rewrite isS2 then nextBound
          let hungTwo: hangsFrom s2 (leavesOf (read2 ++ ((commaReads steps ++ [last]) ++ rest))) = True :=
            rewrite <- twoAssoc then hung2
          let (_, hungAfterTwo) :=
            speltHung innerModes two read2 ((commaReads steps ++ [last]) ++ rest) s2 twoSpelt s2Bound hungTwo
          let roundsBound: bounds innerModes (s2.enters read2).nextItem = True :=
            rewrite isS2, entersNext two read2 t1 twoSpelt then nextBound
          let hungRounds: hangsFrom (s2.enters read2) (leavesOf (commaReads steps ++ [last, ..rest])) = True :=
            rewrite <- stepsAssoc then hungAfterTwo
          let separatorOpen: ∀ (lined: Modes) => QuietModes lined → lined.stops separator = False := lined linedQuiet =>
            deepStops lined separator linedQuiet deepSeparator (rewrite isComma)
          let goal: Goal := { modes = innerModes, level = LevelFull }
          let oneTree: TreeN (Succ below) goal read1 (elements ++ rest) one :=
            inner below
              (arithmetic [])
              innerModes
              one
              read1
              (elements ++ rest)
              s1
              innerQuiet
              (arithmetic [deep])
              oneSpelt
              (Bool.andLeft free)
              line1
              (lineJoin elements rest lineElements facts.lineRest)
              (Inl (rewrite isS1))
              s1Bound
              hung1
              deep1
              (rewrite isComma)
          let twoTree: TreeN (Succ below) goal read2 ((commaReads steps ++ [last]) ++ rest) two :=
            inner below
              (arithmetic [])
              innerModes
              two
              read2
              ((commaReads steps ++ [last]) ++ rest)
              s2
              innerQuiet
              (arithmetic [deep])
              twoSpelt
              (Bool.andLeft (Bool.andRight free))
              line2
              (lineJoin (commaReads steps ++ [last]) rest lineSteps facts.lineRest)
              (Inl (rewrite isS2))
              s2Bound
              hungTwo
              deep2
              (rewrite stepsAssoc then endsSteps others steps last rest stepsSpelt (rewrite isClose))
          let rounds: CommaReads innerModes (tupleEnds innerModes) (TreeN (Succ below) goal) 2 steps [last, ..rest] :=
            tupleStepsHung innerModes innerQuiet others steps 2 last rest below
              (s2.enters read2)
              inner
              (arithmetic [deep])
              stepsSpelt
              (Bool.andRight (Bool.andRight free))
              lineCommas
              (lineJoin [last] rest lineLast facts.lineRest)
              roundsBound
              hungRounds
              deepSteps
              isClose
          let plain: ParenPlain modes [first, ..(read1 ++ elements) ++ rest] := {
            notOutside = rewrite assoc then
              speltOutsideHung modes quiet first one read1
                (elements ++ rest)
                s1
                oneSpelt
                open1
                s1Bound
                hung1
                deep1
                (openHeadOf modes separator
                  ((read2 ++ (commaReads steps ++ [last])) ++ rest)
                  (separatorOpen modes quiet))
                (rewrite isComma),
            noRight =
              let body := read1 ++ ([separator, ..read2] ++ commaReads steps)
              let bodyShape: (read1 ++ elements) ++ rest = body ++ [last, ..rest] :=
                rewrite repeatedly [List.appendAssoc] then byComputing
              rewrite bodyShape then
                rightClosed first body last rest
                  (tupleWalk one two others read1 separator read2 steps oneSpelt isComma twoSpelt stepsSpelt LParen []
                      []
                      [last, ..rest])
                  (lastOf read1 ([separator, ..read2] ++ commaReads steps) [] (before =>
                    rewrite ontoAppend [separator, ..read2] (commaReads steps) before then
                      headPlainCommaReads others steps stepsSpelt
                        (List.reverseOnto [separator, ..read2] before)
                        (speltLast two read2 twoSpelt [separator, ..before])))
                  isClose
          }
          rewrite isRead then
            (
              first,
              read1 ++ elements,
              byComputing,
              open1,
              after first.kind,
              Inr
                (Inr
                  (Inl (
                    read1,
                    separator,
                    read2,
                    steps,
                    last,
                    one,
                    two,
                    byComputing,
                    (rewrite isBare, isOpenWord, isCloseWord, commaDoneSteps others steps two [one] stepsSpelt),
                    isOpen,
                    plain,
                    oneTree,
                    separatorOpen innerModes innerQuiet,
                    isComma,
                    twoTree,
                    rounds,
                    deepStops innerModes last innerQuiet deepLast (rewrite isClose),
                    isClose
                  )))
            )
    | ListOf open [] comma close, (first, last, isRead, isBare, isOpen, isOpenWord, isClose, isCloseWord) =>
      let openItems: openHead modes [first, last] = True := rewrite <- isRead then facts.openFirst
      let open1 := openHeadStops modes first [last] openItems
      let deepItemsNow := facts.deepItems
      let deepList: deepAll [first, last, ..rest] = True := rewrite isRead at deepItemsNow then deepItemsNow
      let deepLast := deepHead last rest (Bool.andRight deepList)
      rewrite isRead then
        (
          first,
          [last],
          byComputing,
          open1,
          after first.kind,
          Inr
            (Inr
              (Inr
                (Inl (
                  last,
                  byComputing,
                  (rewrite isBare, isOpenWord, isCloseWord),
                  isOpen,
                  (rewrite quietPeekSecond modes first last rest open1
                        (deepStops modes last quiet deepLast (rewrite isClose)),
                      isClose),
                  deepStops innerModes last innerQuiet deepLast (rewrite isClose),
                  isClose
                ))))
        )
    | ListOf open [one, ..others] comma close, (first, read1, steps, last, isRead, isBare, isOpen, isOpenWord, isClose,
        isCloseWord, oneSpelt, stepsSpelt) =>
      match depth, deep with
        | Zero, deep => Void.impossible (arithmetic [deep])
        | Succ below, deep =>
          let elements := commaReads steps ++ [last]
          let lineItems: lineAll [first, ..read1 ++ elements] = True := rewrite <- isRead then facts.lineRead
          let openItems: openHead modes [first, ..read1 ++ elements] = True := rewrite <- isRead then facts.openFirst
          let open1 := openHeadStops modes first (read1 ++ elements) openItems
          let (line1, lineElements) := lineSplit read1 elements (Bool.andRight lineItems)
          let (lineCommas, lineLast) := lineSplit (commaReads steps) [last] lineElements
          let assoc: (read1 ++ elements) ++ rest = read1 ++ (elements ++ rest) := List.appendAssoc read1 elements rest
          let shape: read ++ rest = [first, ..read1 ++ (elements ++ rest)] := rewrite isRead, assoc
          let hungItems: hangsFrom state (leavesOf [first, ..read1 ++ (elements ++ rest)]) = True :=
            rewrite <- shape then facts.hung
          let deepItems1: deepAll [first, ..read1 ++ (elements ++ rest)] = True := rewrite <- shape then facts.deepItems
          let deep1: deepAll (read1 ++ (elements ++ rest)) = True := Bool.andRight deepItems1
          let deepElements: deepAll (elements ++ rest) = True := deepRest read1 (elements ++ rest) deep1
          let stepsAssoc: (commaReads steps ++ [last]) ++ rest = commaReads steps ++ [last, ..rest] :=
            List.appendAssoc (commaReads steps) [last] rest
          let deepSteps: deepAll (commaReads steps ++ [last, ..rest]) = True := rewrite <- stepsAssoc then deepElements
          let deepLast := deepHead last rest (deepRest (commaReads steps) [last, ..rest] deepSteps)
          let (s1, steppedOpen, hung1) := hungStep state first.leaf (leavesOf (read1 ++ (elements ++ rest))) hungItems
          let isS1 := hangOpenStep state s1 first.leaf (rewrite isOpen) steppedOpen
          let boundNow := facts.bound
          let enteredBound: bounds modes (state.entered first.leaf) = True := rewrite isRead at boundNow then boundNow
          let s1Bound: bounds modes s1 = True :=
            boundsCong modes s1 (state.entered first.leaf) (rewrite isS1) enteredBound
          let (_, hungAfterOne) := speltHung innerModes one read1 (elements ++ rest) s1 oneSpelt s1Bound hung1
          let roundsBound: bounds innerModes (s1.enters read1).nextItem = True :=
            rewrite entersNextIn one read1 s1 None (state.entered first.leaf).blocks (rewrite isS1) oneSpelt then
              boundsCong innerModes s1.nextItem (state.entered first.leaf) (rewrite isS1) enteredBound
          let hungRounds: hangsFrom (s1.enters read1) (leavesOf (commaReads steps ++ [last, ..rest])) = True :=
            rewrite <- stepsAssoc then hungAfterOne
          let goal: Goal := { modes = innerModes, level = LevelFull }
          let (second, more, isRead1, starts) := speltStarts one read1 oneSpelt
          let (_, notBracket, notSpread) := startNotClose second.kind starts
          let hungSecond: hangsFrom s1 (leavesOf ([second, ..more] ++ (elements ++ rest))) = True :=
            rewrite <- isRead1 then hung1
          let deepSecond: deepAll ([second, ..more] ++ (elements ++ rest)) = True := rewrite <- isRead1 then deep1
          let (open2, _, _) := leadHung modes s1 second (more ++ (elements ++ rest)) quiet starts s1Bound hungSecond
          let (openInner2, _, _) :=
            leadHung innerModes s1 second (more ++ (elements ++ rest)) innerQuiet starts s1Bound hungSecond
          let oneTree: TreeN (Succ below) goal read1 (elements ++ rest) one :=
            inner below
              (arithmetic [])
              innerModes
              one
              read1
              (elements ++ rest)
              s1
              innerQuiet
              (arithmetic [deep])
              oneSpelt
              (Bool.andLeft free)
              line1
              (lineJoin elements rest lineElements facts.lineRest)
              (Inl (rewrite isS1))
              s1Bound
              hung1
              deep1
              (rewrite stepsAssoc then endsSteps others steps last rest stepsSpelt (rewrite isClose))
          let rounds: CommaReads innerModes
            (count => innerModes.at RBracket)
            (ListElement (TreeN (Succ below)) innerModes)
            1
            steps
            [last, ..rest] :=
            listStepsHung innerModes innerQuiet others steps 1 last rest below
              (s1.enters read1)
              inner
              (arithmetic [deep])
              stepsSpelt
              (Bool.andRight free)
              lineCommas
              (lineJoin [last] rest lineLast facts.lineRest)
              roundsBound
              hungRounds
              deepSteps
              isClose
          let kinds: exprAll [second, ..more] = True := rewrite <- isRead1 then speltExpr one read1 oneSpelt
          let (kind, peek2, kindExpr) :=
            peekTwoHung modes quiet first second more
              (elements ++ rest)
              s1
              open1
              starts
              s1Bound
              hungSecond
              deepSecond
              (openStepsHung modes quiet others steps last rest stepsSpelt (rewrite isClose) deepElements)
              (Bool.andRight kinds)
              (exprHeadSteps others steps last rest stepsSpelt (rewrite isClose))
          let firstPeek: peekIn innerModes 0 ((read1 ++ elements) ++ rest) = Some second.kind :=
            rewrite assoc, isRead1 then peekFirst innerModes second (more ++ (elements ++ rest)) openInner2
          let elementPeek: peekIn innerModes 0 (read1 ++ (elements ++ rest)) = Some second.kind :=
            rewrite isRead1 then peekFirst innerModes second (more ++ (elements ++ rest)) openInner2
          rewrite isRead then
            (
              first,
              read1 ++ elements,
              byComputing,
              open1,
              after first.kind,
              Inr
                (Inr
                  (Inr
                    (Inr
                      (Inl (
                        read1,
                        steps,
                        last,
                        one,
                        byComputing,
                        (rewrite isBare, isOpenWord, isCloseWord, commaDoneSteps others steps one [] stepsSpelt),
                        isOpen,
                        (rewrite assoc,
                            isRead1,
                            quietPeekSecond modes first second (more ++ (elements ++ rest)) open1 open2,
                            peek2 then
                          startBracketPlain second.kind kind starts kindExpr),
                        (rewrite firstPeek then notBracket),
                        ((rewrite elementPeek then notSpread), oneTree),
                        rounds,
                        deepStops innerModes last innerQuiet deepLast (rewrite isClose),
                        isClose
                      )))))
            )
    | App _ _ | Prefix _ _ | Infix _ _ _ _, _ => (Bool.falseNotTrue atomic).impossible
    | _, never => Void.impossible never

--| A tuple's items after the first two, each after its comma, then the closer: `state` is the line rule's before the
--| first comma, and the modes are bounded at the start of a bracket's item (`nextItem`).
--|
--| Proof idea: by induction on the items: the comma steps to the start of the next item (`commaNext`), `fullHung`
--| reads it, and after it the next item's start is the same (`entersNext`), so the bound carries.
theorem tupleStepsHung ∀ (modes: Modes)
    (quiet: QuietModes modes)
    (exprs: List Expr) (steps: List (Item, List Item, Expr)) (count: Nat) (last: Item) (rest: List Item)
    (depth: Nat) (state: HangState)
    (inner: FullHungBelow (Succ depth))
    (deep: nestAll exprs <= depth)
    (spelt: SpeltSteps exprs steps)
    (free: autoPlacedAll True exprs = True)
    (lineSteps: lineAll (commaReads steps) = True)
    (lineRest: lineAll [last, ..rest] = True)
    (bound: bounds modes state.nextItem = True)
    (hung: hangsFrom state (leavesOf (commaReads steps ++ [last, ..rest])) = True)
    (deepItems: deepAll (commaReads steps ++ [last, ..rest]) = True)
    (isClose: last.kind = RParen):
    CommaReads modes (tupleEnds modes) (TreeN (Succ depth) { modes, level = LevelFull }) count steps [last, ..rest] :=
  match exprs, spelt with
    | [], isEmpty =>
      let deepLast: deepAll [last, ..rest] = True := rewrite isEmpty at deepItems then deepItems
      rewrite isEmpty,
          peekFirst modes last rest (deepStops modes last quiet (deepHead last rest deepLast) (rewrite isClose)),
          isClose
    | [expr, ..more], (comma, read, later, isSteps, isComma, exprSpelt, moreSpelt) =>
      let tail := commaReads later ++ [last, ..rest]
      let lineAll1: lineAll [comma, ..read ++ commaReads later] = True :=
        Eq.trans (Eq.cong (taken => lineAll (commaReads taken)) isSteps).flipped lineSteps
      let (lineRead, lineLater) := lineSplit read (commaReads later) (Bool.andRight lineAll1)
      let shape: commaReads steps ++ [last, ..rest] = [comma, ..read ++ tail] :=
        rewrite isSteps, List.appendAssoc read (commaReads later) [last, ..rest]
      let hungAll: hangsFrom state (leavesOf [comma, ..read ++ tail]) = True := rewrite <- shape then hung
      let deepAll1: deepAll [comma, ..read ++ tail] = True := rewrite <- shape then deepItems
      let deepRead: deepAll (read ++ tail) = True := Bool.andRight deepAll1
      let (next, steppedComma, hungNext) := hungStep state comma.leaf (leavesOf (read ++ tail)) hungAll
      let isNext := commaNext state next comma.leaf (rewrite isComma) steppedComma
      let hungItem: hangsFrom state.nextItem (leavesOf (read ++ tail)) = True := rewrite <- isNext then hungNext
      let (first, inside, isRead, starts) := speltStarts expr read exprSpelt
      let hungFirst: hangsFrom state.nextItem (leavesOf ([first, ..inside] ++ tail)) = True :=
        rewrite <- isRead then hungItem
      let (openFirst, _, _) := leadHung modes state.nextItem first (inside ++ tail) quiet starts bound hungFirst
      let (notClose, _, _) := startNotClose first.kind starts
      let (_, hungAfter) := speltHung modes expr read tail state.nextItem exprSpelt bound hungItem
      let nextBound: bounds modes (state.nextItem.enters read).nextItem = True :=
        rewrite entersNext expr read state exprSpelt then bound
      rewrite isSteps then
        (
          deepStops modes comma quiet (deepHead comma (read ++ tail) deepAll1) (rewrite isComma),
          isComma,
          runsTupleEndsGo modes count
            (read ++ tail)
            (rewrite isRead, peekFirst modes first (inside ++ tail) openFirst then notClose),
          inner depth
            (arithmetic [])
            modes
            expr
            read
            tail
            state.nextItem
            quiet
            (arithmetic [deep])
            exprSpelt
            (Bool.andLeft free)
            lineRead
            (lineJoin (commaReads later) [last, ..rest] lineLater lineRest)
            (Inl byComputing)
            bound
            hungItem
            deepRead
            (endsSteps more later last rest moreSpelt (rewrite isClose)),
          tupleStepsHung modes quiet more later
            (count + 1)
            last
            rest
            depth
            (state.nextItem.enters read)
            inner
            (arithmetic [deep])
            moreSpelt
            (Bool.andRight free)
            lineLater
            lineRest
            nextBound
            hungAfter
            (deepRest read tail deepRead)
            isClose
        )

--| A list's items after the first, likewise.
--|
--| Proof idea: as `tupleStepsHung`, with the item's first kind neither `]` nor `..`.
theorem listStepsHung ∀ (modes: Modes)
    (quiet: QuietModes modes)
    (exprs: List Expr) (steps: List (Item, List Item, Expr)) (count: Nat) (last: Item) (rest: List Item)
    (depth: Nat) (state: HangState)
    (inner: FullHungBelow (Succ depth))
    (deep: nestAll exprs <= depth)
    (spelt: SpeltSteps exprs steps)
    (free: autoPlacedAll True exprs = True)
    (lineSteps: lineAll (commaReads steps) = True)
    (lineRest: lineAll [last, ..rest] = True)
    (bound: bounds modes state.nextItem = True)
    (hung: hangsFrom state (leavesOf (commaReads steps ++ [last, ..rest])) = True)
    (deepItems: deepAll (commaReads steps ++ [last, ..rest]) = True)
    (isClose: last.kind = RBracket):
    CommaReads modes (count => modes.at RBracket) (ListElement (TreeN (Succ depth)) modes) count steps [last, ..rest] :=
  match exprs, spelt with
    | [], isEmpty =>
      let deepLast: deepAll [last, ..rest] = True := rewrite isEmpty at deepItems then deepItems
      rewrite isEmpty,
          peekFirst modes last rest (deepStops modes last quiet (deepHead last rest deepLast) (rewrite isClose)),
          isClose
    | [expr, ..more], (comma, read, later, isSteps, isComma, exprSpelt, moreSpelt) =>
      let tail := commaReads later ++ [last, ..rest]
      let lineAll1: lineAll [comma, ..read ++ commaReads later] = True :=
        Eq.trans (Eq.cong (taken => lineAll (commaReads taken)) isSteps).flipped lineSteps
      let (lineRead, lineLater) := lineSplit read (commaReads later) (Bool.andRight lineAll1)
      let shape: commaReads steps ++ [last, ..rest] = [comma, ..read ++ tail] :=
        rewrite isSteps, List.appendAssoc read (commaReads later) [last, ..rest]
      let hungAll: hangsFrom state (leavesOf [comma, ..read ++ tail]) = True := rewrite <- shape then hung
      let deepAll1: deepAll [comma, ..read ++ tail] = True := rewrite <- shape then deepItems
      let deepRead: deepAll (read ++ tail) = True := Bool.andRight deepAll1
      let (next, steppedComma, hungNext) := hungStep state comma.leaf (leavesOf (read ++ tail)) hungAll
      let isNext := commaNext state next comma.leaf (rewrite isComma) steppedComma
      let hungItem: hangsFrom state.nextItem (leavesOf (read ++ tail)) = True := rewrite <- isNext then hungNext
      let (first, inside, isRead, starts) := speltStarts expr read exprSpelt
      let hungFirst: hangsFrom state.nextItem (leavesOf ([first, ..inside] ++ tail)) = True :=
        rewrite <- isRead then hungItem
      let (openFirst, _, _) := leadHung modes state.nextItem first (inside ++ tail) quiet starts bound hungFirst
      let (_, notBracket, notSpread) := startNotClose first.kind starts
      let firstPeek: peekIn modes 0 (read ++ tail) = Some first.kind :=
        rewrite isRead then peekFirst modes first (inside ++ tail) openFirst
      let (_, hungAfter) := speltHung modes expr read tail state.nextItem exprSpelt bound hungItem
      let nextBound: bounds modes (state.nextItem.enters read).nextItem = True :=
        rewrite entersNext expr read state exprSpelt then bound
      rewrite isSteps then
        (
          deepStops modes comma quiet (deepHead comma (read ++ tail) deepAll1) (rewrite isComma),
          isComma,
          (rewrite <- (rewrite firstPeek then notBracket: isSome RBracket (peekIn modes 0 (read ++ tail)) = False) then
            runsAtOn modes RBracket (read ++ tail)),
          (
            (rewrite firstPeek then notSpread),
            inner depth
              (arithmetic [])
              modes
              expr
              read
              tail
              state.nextItem
              quiet
              (arithmetic [deep])
              exprSpelt
              (Bool.andLeft free)
              lineRead
              (lineJoin (commaReads later) [last, ..rest] lineLater lineRest)
              (Inl byComputing)
              bound
              hungItem
              deepRead
              (endsSteps more later last rest moreSpelt (rewrite isClose))
          ),
          listStepsHung modes quiet more later
            (count + 1)
            last
            rest
            depth
            (state.nextItem.enters read)
            inner
            (arithmetic [deep])
            moreSpelt
            (Bool.andRight free)
            lineLater
            lineRest
            nextBound
            hungAfter
            (deepRest read tail deepRead)
            isClose
        )

--| After a bracket's items, the next comma or the closer doesn't stop a reading: each is inside the bracket
--| (`deepItems`), where the parser's line test exempts it.
theorem openStepsHung ∀ (modes: Modes)
    (quiet: QuietModes modes)
    (exprs: List Expr) (steps: List (Item, List Item, Expr)) (last: Item) (rest: List Item)
    (spelt: SpeltSteps exprs steps)
    (closer: last.kind.isCloser = True)
    (deepItems: deepAll ((commaReads steps ++ [last]) ++ rest) = True):
    openHead modes ((commaReads steps ++ [last]) ++ rest) = True :=
  match exprs, spelt with
    | [], isEmpty =>
      let deepLast: deepAll [last, ..rest] = True := rewrite isEmpty at deepItems then deepItems
      rewrite isEmpty then
        openHeadOf modes last rest
          (deepStops modes last quiet (deepHead last rest deepLast) (rewrite closer then Bool.orTrue _))
    | [_, .._], (comma, read, later, isSteps, isComma, _, _) =>
      let deepFirst: deepAll [comma, ..((read ++ commaReads later) ++ [last]) ++ rest] = True :=
        rewrite isSteps at deepItems then deepItems
      rewrite isSteps, deepStops modes comma quiet (deepHead comma _ deepFirst) (rewrite isComma)
