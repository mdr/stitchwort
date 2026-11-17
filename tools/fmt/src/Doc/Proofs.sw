--| The printer's budgets are enough. `print` gives the printer 3 steps per
--| node of the document, and 3 more, and gives every `fits` it asks the
--| same budget. Every printer step takes a command off its work list or
--| replaces it by commands that weigh less (`Doc.steps`), so the work list
--| runs out first; and what `fits` can read, the node it measures and the
--| work list after it, never weighs more than the work list did at the
--| start (`Cmd.weight`), so `fits` never runs out either, where it would
--| answer "fits" without looking. Any larger budget prints the same text.

namespace Fmt.Doc.Proofs
import Fmt.Doc (..)
import Std (Bool, List, Nat, Option, Text, Void)

--| The steps the printer can still take on `doc`, at most: a step on a
--| node replaces it by its parts, which weigh less.
def Doc.steps: Doc → Nat
  | Nest _ inner => 1 + inner.steps
  | Group inner _ => 1 + inner.steps
  | Flatten inner => 1 + inner.steps
  | OneLineBelow inner => 2 + inner.steps
  | Concat docs => 1 + stepsOf docs
  | Fill items => 1 + stepsOf items + items.length
  | Choice options => 2 + stepsOf options
  | _ => 1

def stepsOf: List Doc → Nat
  | [] => 0
  | [doc, ..docs] => doc.steps + stepsOf docs

def Cmd.cost: Cmd → Nat
  | Print _ _ doc => doc.steps
  | FillSep _ item => item.steps + 1

def stackCost: List Cmd → Nat
  | [] => 0
  | [cmd, ..rest] => cmd.cost + stackCost rest

theorem stepsPositive ∀ (doc: Doc): 1 ≤ doc.steps := match doc with
  | Nest more inner => arithmetic
  | Group inner hard => arithmetic
  | Flatten inner => arithmetic
  | OneLineBelow inner => arithmetic
  | Concat docs => arithmetic
  | Fill items => arithmetic
  | Choice options => arithmetic
  | _ => arithmetic

theorem stackCostAppend ∀ (front back: List Cmd): stackCost (front ++ back) = stackCost front + stackCost back :=
  match front with
    | [] => byComputing
    | [cmd, ..rest] => rewrite stackCostAppend rest back then arithmetic

theorem costPrints ∀ (indent: Nat) (mode: Mode) (docs: List Doc):
    stackCost (docs.map (Print indent mode)) = stepsOf docs :=
  match docs with
    | [] => byComputing
    | [doc, ..rest] => rewrite costPrints indent mode rest

theorem costFillSeps ∀ (indent: Nat) (items: List Doc):
    stackCost (items.map (FillSep indent)) = stepsOf items + items.length :=
  match items with
    | [] => byComputing
    | [item, ..rest] => rewrite costFillSeps indent rest then arithmetic

theorem joinLinesSteps ∀ (items: List Doc): stepsOf (Doc.joinLines items) ≤ stepsOf items + items.length :=
  match items with
    | [] => arithmetic
    | [only] => arithmetic
    | [item, next, ..rest] =>
      let tail := joinLinesSteps [next, ..rest]
      arithmetic

theorem headOrSteps ∀ (options: List Doc): (options.headOr Empty).steps ≤ stepsOf options + 1 := match options with
  | [] => arithmetic
  | [option, ..rest] => arithmetic

theorem ifStepsBound ∀ (condition: Bool) (yes no: Doc) (bound: Nat)
    (yesBound: yes.steps ≤ bound)
    (noBound: no.steps ≤ bound):
    (if condition then yes else no).steps ≤ bound :=
  match condition with
    | True => yesBound
    | False => noBound

theorem chooseSteps ∀ (printer: Printer) (total indent: Nat) (rest: List Cmd) (options: List Doc):
    (printer.choose total indent rest options).steps ≤ stepsOf options + 1 :=
  match options with
    | [] => arithmetic
    | [last] => arithmetic
    | [option, next, ..others] =>
      let later := chooseSteps printer total indent rest [next, ..others]
      ifStepsBound _ option (printer.choose total indent rest [next, ..others]) _ (arithmetic) (arithmetic [later])

theorem ifPairBound ∀ (condition: Bool) (yes no: (Printer, List Cmd)) (bound: Nat)
    (yesBound: stackCost yes.snd < bound)
    (noBound: stackCost no.snd < bound):
    stackCost (if condition then yes else no).snd < bound :=
  match condition with
    | True => yesBound
    | False => noBound

--| Every step weighs the work list down.
theorem stepLighter ∀ (printer: Printer) (total: Nat) (cmd: Cmd) (rest: List Cmd):
    stackCost (printer.step total cmd rest).snd < cmd.cost + stackCost rest :=
  match cmd with
    | FillSep indent item =>
      ifPairBound _
        (printer.write indent " " 1, [Print indent Flat item, ..rest])
        (printer.newline indent, [Print indent Break item, ..rest])
        (item.steps + 1 + stackCost rest)
        (arithmetic)
        (arithmetic)
    | Print indent mode doc =>
      match doc with
        | Empty => arithmetic
        | BreakParent => arithmetic
        | Chunk text width => arithmetic
        | Closing text => arithmetic
        | Line =>
          ifPairBound _
            (printer.write indent " " 1, rest)
            (printer.newline indent, rest)
            (1 + stackCost rest)
            (arithmetic)
            (arithmetic)
        | SoftLine =>
          ifPairBound _ (printer, rest) (printer.newline indent, rest) (1 + stackCost rest) (arithmetic) (arithmetic)
        | HardLine => arithmetic
        | LineStart => arithmetic
        | CommentEnd => arithmetic
        | LineStartHere =>
          ifPairBound _
            ({ printer | owed = Some indent, lineIndent = indent }, rest)
            (printer.newline indent, rest)
            (1 + stackCost rest)
            (arithmetic)
            (arithmetic)
        | Blank => arithmetic
        | LineSuffix comment => arithmetic
        | Nest more inner => arithmetic
        | OneLineBelow inner => arithmetic
        | Flatten inner => arithmetic
        | Group inner hard => arithmetic
        | Concat docs =>
          rewrite stackCostAppend (docs.map (Print indent mode)) rest, costPrints indent mode docs then arithmetic
        | Fill items =>
          match items with
            | [] => arithmetic
            | [first, ..others] =>
              match mode with
                | Flat =>
                  let joinedLines := Doc.joinLines [first, ..others]
                  let bound := joinLinesSteps [first, ..others]
                  rewrite stackCostAppend (joinedLines.map (Print indent Flat)) rest,
                      costPrints indent Flat joinedLines then
                    arithmetic
                | Break =>
                  rewrite stackCostAppend (others.map (FillSep indent)) rest, costFillSeps indent others then arithmetic
        | Choice options =>
          match mode with
            | Flat =>
              let bound := headOrSteps options
              arithmetic
            | Break =>
              let bound := chooseSteps printer total indent rest options
              arithmetic

theorem costPositive ∀ (cmd: Cmd): 1 ≤ cmd.cost := match cmd with
  | Print indent mode doc => stepsPositive doc
  | FillSep indent item => arithmetic

--| Once the fuel covers the work list's weight, more fuel prints the same:
--| the work list runs out first.
theorem runFuelEnough ∀ (printer: Printer) (total fuel extra: Nat) (stack: List Cmd)
    (enough: stackCost stack ≤ fuel):
    printer.run total (fuel + extra) stack = printer.run total fuel stack :=
  match fuel, stack with
    | Zero, [] =>
      match extra with
        | Zero => byComputing
        | Succ more => byComputing
    | Succ more, [] => byComputing
    | Zero, [cmd, ..rest] =>
      let positive := costPositive cmd
      Void.impossible (arithmetic)
    | Succ more, [cmd, ..rest] =>
      let lighter := stepLighter printer total cmd rest
      match stepped: printer.step total cmd rest with
        | (next, stack) => runFuelEnough next total more extra stack (arithmetic)

theorem sizePositive ∀ (doc: Doc): 1 ≤ doc.size := match doc with
  | Nest more inner => arithmetic
  | Group inner hard => arithmetic
  | Flatten inner => arithmetic
  | OneLineBelow inner => arithmetic
  | Concat docs => arithmetic
  | Fill items => arithmetic
  | Choice options => arithmetic
  | _ => arithmetic

theorem lengthUnderSizes ∀ (docs: List Doc): docs.length ≤ Doc.sizes docs := match docs with
  | [] => arithmetic
  | [doc, ..rest] =>
    let head := sizePositive doc
    let tail := lengthUnderSizes rest
    arithmetic

theorem stepsUnderSize ∀ (doc: Doc): doc.steps ≤ 2 * doc.size := match doc with
  | Nest more inner =>
    let inside := stepsUnderSize inner
    arithmetic
  | Group inner hard =>
    let inside := stepsUnderSize inner
    arithmetic
  | Flatten inner =>
    let inside := stepsUnderSize inner
    arithmetic
  | OneLineBelow inner =>
    let inside := stepsUnderSize inner
    arithmetic
  | Concat docs =>
    let inside := stepsOfUnderSizes docs
    arithmetic
  | Fill items =>
    let inside := stepsOfUnderSizes items
    let count := lengthUnderSizes items
    arithmetic
  | Choice options =>
    let inside := stepsOfUnderSizes options
    arithmetic
  | Empty => arithmetic
  | BreakParent => arithmetic
  | Chunk text width => arithmetic
  | Closing text => arithmetic
  | Line => arithmetic
  | SoftLine => arithmetic
  | HardLine => arithmetic
  | LineStart => arithmetic
  | CommentEnd => arithmetic
  | LineStartHere => arithmetic
  | Blank => arithmetic
  | LineSuffix comment => arithmetic

theorem stepsOfUnderSizes ∀ (docs: List Doc): stepsOf docs ≤ 2 * Doc.sizes docs := match docs with
  | [] => arithmetic
  | [doc, ..rest] =>
    let head := stepsUnderSize doc
    let tail := stepsOfUnderSizes rest
    arithmetic

--| `print`'s step budget, three steps per node and three more, is enough:
--| the printer runs out of work before it runs out of steps, so any larger
--| budget prints the same.
theorem printStepsEnough ∀ (printer: Printer) (total extra: Nat) (doc: Doc) (indent: Nat) (mode: Mode):
    printer.run total (3 * doc.size + 3 + extra) [Print indent mode doc]
      = printer.run total (3 * doc.size + 3) [Print indent mode doc] :=
  let bound := stepsUnderSize doc
  runFuelEnough printer total (3 * doc.size + 3) extra [Print indent mode doc] (arithmetic)

--| The steps `fits` can take measuring `stack`.
def pairSteps: List (Nat, Mode, Doc) → Nat
  | [] => 0
  | [(_, _, doc), ..stack] => doc.steps + pairSteps stack

--| The steps `fits` can take reading on into the work list, up to the
--| first fill separator, where it stops.
def restNeed: List Cmd → Nat
  | [Print _ _ doc, ..others] => 1 + doc.steps + restNeed others
  | _ => 0

def fitsNeed (stack: List (Nat, Mode, Doc)) (rest: List Cmd): Nat := pairSteps stack + restNeed rest

theorem pairStepsMap ∀ (indent: Nat) (mode: Mode) (docs: List Doc) (stack: List (Nat, Mode, Doc)):
    pairSteps (docs.map (inner => (indent, mode, inner)) ++ stack) = stepsOf docs + pairSteps stack :=
  match docs with
    | [] => byComputing
    | [doc, ..rest] => rewrite pairStepsMap indent mode rest stack then arithmetic

theorem lastSteps ∀ (options: List Doc) (option: Doc)
    (picked: options.last = Some option):
    option.steps ≤ stepsOf options :=
  match options with
    | [only] => rewrite <- Option.someInjective picked then arithmetic
    | [first, second, ..others] =>
      let later := lastSteps [second, ..others] option picked
      arithmetic

theorem headSteps ∀ (options: List Doc) (option: Doc)
    (picked: options.head = Some option):
    option.steps ≤ stepsOf options :=
  match options with | [first, ..others] => rewrite <- Option.someInjective picked then arithmetic

--| With fuel for every step it could take, `fits` gives the same answer
--| as with more: it never stops for want of fuel, where it would answer
--| "fits" without looking.
theorem fitsFromEnough ∀ (fuel extra width: Nat) (stack: List (Nat, Mode, Doc)) (rest: List Cmd)
    (left lineIndent: Nat) (suffix: Bool)
    (enough: fitsNeed stack rest ≤ fuel):
    fitsFrom (fuel + extra) width stack rest left lineIndent suffix
      = fitsFrom fuel width stack rest left lineIndent suffix :=
  match fuel with
    | Zero =>
      match stack, rest with
        | [], [] =>
          match extra with
            | Zero => byComputing
            | Succ more => byComputing
        | [], [FillSep indent item, ..others] =>
          match extra with
            | Zero => byComputing
            | Succ more => byComputing
        | [(indent, mode, doc), ..stack], _ =>
          let positive := stepsPositive doc
          Void.impossible (arithmetic)
    | Succ more =>
      match stack with
        | [] =>
          match rest with
            | [] => byComputing
            | [FillSep indent item, ..others] => byComputing
            | [Print indent mode doc, ..others] =>
              rewrite fitsFromEnough more extra width [(indent, mode, doc)] others left lineIndent suffix (arithmetic)
        | [(indent, mode, doc), ..stack] =>
          let same := (at to: Nat) (waits: Bool) (fewer: fitsNeed stack rest ≤ more) =>
            fitsFromEnough more extra width stack rest at to waits fewer
          match doc with
            | Empty => rewrite same left lineIndent suffix (arithmetic)
            | Blank => rewrite same left lineIndent suffix (arithmetic)
            | LineSuffix comment => rewrite same left lineIndent True (arithmetic)
            | BreakParent => rewrite same left lineIndent suffix (arithmetic)
            | Chunk text textWidth =>
              match suffix with
                | False => rewrite same (left - textWidth) lineIndent False (arithmetic)
                | True =>
                  match spaces: text.all (char => char == ' ') with
                    | True => rewrite same left lineIndent True (arithmetic)
                    | False =>
                      let broken := Nat.max indent (lineIndent + 2)
                      rewrite same (width - broken - textWidth) broken False (arithmetic)
            | Closing text => rewrite same (left - text.length) lineIndent suffix (arithmetic)
            | Line => rewrite same (left - 1) lineIndent suffix (arithmetic)
            | SoftLine => rewrite same left lineIndent suffix (arithmetic)
            | HardLine => byComputing
            | LineStart => byComputing
            | CommentEnd => byComputing
            | LineStartHere => byComputing
            | Nest extraIndent inner =>
              rewrite fitsFromEnough more extra width
                [(indent + extraIndent, mode, inner), ..stack]
                rest
                left
                lineIndent
                suffix
                (arithmetic)
            | Flatten inner =>
              rewrite fitsFromEnough more extra width
                [(indent, Flat, inner), ..stack]
                rest
                left
                lineIndent
                suffix
                (arithmetic)
            | Group inner hard =>
              let measured := if hard then Break else mode
              rewrite fitsFromEnough more extra width
                [(indent, measured, inner), ..stack]
                rest
                left
                lineIndent
                suffix
                (arithmetic)
            | Concat docs =>
              let laid := pairStepsMap indent mode docs stack
              rewrite fitsFromEnough more extra width
                (docs.map (inner => (indent, mode, inner)) ++ stack)
                rest
                left
                lineIndent
                suffix
                (arithmetic)
            | Fill items =>
              match mode with
                | Flat =>
                  let joinedLines := Doc.joinLines items
                  let laid := pairStepsMap indent Flat joinedLines stack
                  let bound := joinLinesSteps items
                  rewrite fitsFromEnough more extra width
                    (joinedLines.map (inner => (indent, Flat, inner)) ++ stack)
                    rest
                    left
                    lineIndent
                    suffix
                    (arithmetic)
                | Break =>
                  match items with
                    | [] => byComputing
                    | [first, ..others] =>
                      rewrite fitsFromEnough more extra width
                        [(indent, Flat, first)]
                        []
                        left
                        lineIndent
                        suffix
                        (arithmetic)
            | OneLineBelow inner => byComputing
            | Choice options =>
              match mode with
                | Flat =>
                  match picked: options.head with
                    | None => rewrite same left lineIndent suffix (arithmetic)
                    | Some option =>
                      let bound := headSteps options option picked
                      rewrite fitsFromEnough more extra width
                        [(indent, Flat, option), ..stack]
                        rest
                        left
                        lineIndent
                        suffix
                        (arithmetic)
                | Break =>
                  match picked: options.last with
                    | None => rewrite same left lineIndent suffix (arithmetic)
                    | Some option =>
                      let bound := lastSteps options option picked
                      rewrite fitsFromEnough more extra width
                        [(indent, Break, option), ..stack]
                        rest
                        left
                        lineIndent
                        suffix
                        (arithmetic)

--| What the work list can still cost `fits`, all calls together: a
--| command's steps, and one more step for each node, which reading it out
--| of the work list costs.
def Cmd.weight: Cmd → Nat
  | Print _ _ doc => doc.steps + doc.size
  | FillSep _ item => item.steps + 1 + item.size

def stackWeight: List Cmd → Nat
  | [] => 0
  | [cmd, ..rest] => cmd.weight + stackWeight rest

theorem stackWeightAppend ∀ (front back: List Cmd):
    stackWeight (front ++ back) = stackWeight front + stackWeight back :=
  match front with
    | [] => byComputing
    | [cmd, ..rest] => rewrite stackWeightAppend rest back then arithmetic

theorem weightPrints ∀ (indent: Nat) (mode: Mode) (docs: List Doc):
    stackWeight (docs.map (Print indent mode)) = stepsOf docs + Doc.sizes docs :=
  match docs with
    | [] => byComputing
    | [doc, ..rest] => rewrite weightPrints indent mode rest then arithmetic

theorem weightFillSeps ∀ (indent: Nat) (items: List Doc):
    stackWeight (items.map (FillSep indent)) = stepsOf items + items.length + Doc.sizes items :=
  match items with
    | [] => byComputing
    | [item, ..rest] => rewrite weightFillSeps indent rest then arithmetic

theorem joinLinesSizes ∀ (items: List Doc): Doc.sizes (Doc.joinLines items) ≤ Doc.sizes items + items.length :=
  match items with
    | [] => arithmetic
    | [only] => arithmetic
    | [item, next, ..rest] =>
      let tail := joinLinesSizes [next, ..rest]
      arithmetic

theorem headOrSize ∀ (options: List Doc): (options.headOr Empty).size ≤ Doc.sizes options + 1 := match options with
  | [] => arithmetic
  | [option, ..rest] => arithmetic

theorem ifBothBound ∀ (condition: Bool) (yes no: Doc) (bound: Nat)
    (yesBound: yes.steps + yes.size ≤ bound)
    (noBound: no.steps + no.size ≤ bound):
    (if condition then yes else no).steps + (if condition then yes else no).size ≤ bound :=
  match condition with
    | True => yesBound
    | False => noBound

theorem chooseWeight ∀ (printer: Printer) (total indent: Nat) (rest: List Cmd) (options: List Doc):
    (printer.choose total indent rest options).steps + (printer.choose total indent rest options).size
      ≤ stepsOf options + Doc.sizes options + 2 :=
  match options with
    | [] => arithmetic
    | [last] => arithmetic
    | [option, next, ..others] =>
      let later := chooseWeight printer total indent rest [next, ..others]
      ifBothBound _ option (printer.choose total indent rest [next, ..others]) _ (arithmetic) (arithmetic [later])

theorem ifPairWeight ∀ (condition: Bool) (yes no: (Printer, List Cmd)) (bound: Nat)
    (yesBound: stackWeight yes.snd ≤ bound)
    (noBound: stackWeight no.snd ≤ bound):
    stackWeight (if condition then yes else no).snd ≤ bound :=
  match condition with
    | True => yesBound
    | False => noBound

--| No step makes the work list heavier for `fits`.
theorem stepWeight ∀ (printer: Printer) (total: Nat) (cmd: Cmd) (rest: List Cmd):
    stackWeight (printer.step total cmd rest).snd ≤ cmd.weight + stackWeight rest :=
  match cmd with
    | FillSep indent item =>
      ifPairWeight _
        (printer.write indent " " 1, [Print indent Flat item, ..rest])
        (printer.newline indent, [Print indent Break item, ..rest])
        (item.steps + 1 + item.size + stackWeight rest)
        (arithmetic)
        (arithmetic)
    | Print indent mode doc =>
      match doc with
        | Empty => arithmetic
        | BreakParent => arithmetic
        | Chunk text width => arithmetic
        | Closing text => arithmetic
        | Line =>
          ifPairWeight _
            (printer.write indent " " 1, rest)
            (printer.newline indent, rest)
            (2 + stackWeight rest)
            (arithmetic)
            (arithmetic)
        | SoftLine =>
          ifPairWeight _ (printer, rest) (printer.newline indent, rest) (2 + stackWeight rest) (arithmetic) (arithmetic)
        | HardLine => arithmetic
        | LineStart => arithmetic
        | CommentEnd => arithmetic
        | LineStartHere =>
          ifPairWeight _
            ({ printer | owed = Some indent, lineIndent = indent }, rest)
            (printer.newline indent, rest)
            (2 + stackWeight rest)
            (arithmetic)
            (arithmetic)
        | Blank => arithmetic
        | LineSuffix comment => arithmetic
        | Nest more inner => arithmetic
        | OneLineBelow inner => arithmetic
        | Flatten inner => arithmetic
        | Group inner hard => arithmetic
        | Concat docs =>
          rewrite stackWeightAppend (docs.map (Print indent mode)) rest, weightPrints indent mode docs then arithmetic
        | Fill items =>
          match items with
            | [] => arithmetic
            | [first, ..others] =>
              match mode with
                | Flat =>
                  let joinedLines := Doc.joinLines [first, ..others]
                  let bound := joinLinesSteps [first, ..others]
                  let sized := joinLinesSizes [first, ..others]
                  let count := lengthUnderSizes [first, ..others]
                  rewrite stackWeightAppend (joinedLines.map (Print indent Flat)) rest,
                      weightPrints indent Flat joinedLines then
                    arithmetic
                | Break =>
                  let count := lengthUnderSizes others
                  rewrite stackWeightAppend (others.map (FillSep indent)) rest, weightFillSeps indent others then
                    arithmetic
        | Choice options =>
          match mode with
            | Flat =>
              let bound := headOrSteps options
              let sized := headOrSize options
              arithmetic
            | Break =>
              let bound := chooseWeight printer total indent rest options
              arithmetic

theorem restNeedUnder ∀ (rest: List Cmd): restNeed rest ≤ stackWeight rest := match rest with
  | [] => arithmetic
  | [FillSep indent item, ..others] => arithmetic
  | [Print indent mode doc, ..others] =>
    let positive := sizePositive doc
    let tail := restNeedUnder others
    arithmetic

theorem chooseEnough ∀ (printer: Printer) (total extra indent: Nat) (rest: List Cmd) (options: List Doc)
    (enough: stepsOf options + restNeed rest ≤ total):
    printer.choose (total + extra) indent rest options = printer.choose total indent rest options :=
  match options with
    | [option, next, ..others] =>
      let later := chooseEnough printer total extra indent rest [next, ..others] (arithmetic)
      match option with
        | OneLineBelow inner =>
          rewrite fitsFromEnough total extra printer.width
                [(indent + 2, Flat, inner)]
                []
                (printer.width - indent - 2)
                (indent + 2)
                False
                (arithmetic),
              later
        | _ =>
          rewrite fitsFromEnough total extra printer.width
                [(indent, Break, option)]
                rest
                printer.left
                printer.lineIndent
                (not printer.suffixes.isEmpty)
                (arithmetic),
              later
    | _ => cases

--| With `fits`'s budget covering the work list's weight, a step takes the
--| same choices as with a larger budget.
theorem stepEnough ∀ (printer: Printer) (total extra: Nat) (cmd: Cmd) (rest: List Cmd)
    (enough: cmd.weight + stackWeight rest ≤ total):
    printer.step (total + extra) cmd rest = printer.step total cmd rest :=
  let under := restNeedUnder rest
  match cmd with
    | FillSep indent item =>
      rewrite fitsFromEnough total extra printer.width
        [(indent, Flat, item)]
        rest
        (printer.left - 1)
        printer.lineIndent
        False
        (arithmetic)
    | Print indent mode doc =>
      match doc with
        | Group inner hard =>
          rewrite fitsFromEnough total extra printer.width
            [(indent, Flat, inner)]
            rest
            printer.left
            printer.lineIndent
            (not printer.suffixes.isEmpty)
            (arithmetic)
        | Fill items =>
          match items with
            | [] => byComputing
            | [first, ..others] =>
              let stack := others.map (FillSep indent) ++ rest
              let laid := stackWeightAppend (others.map (FillSep indent)) rest
              let seps := weightFillSeps indent others
              let need := restNeedUnder stack
              rewrite fitsFromEnough total extra printer.width
                [(indent, Flat, first)]
                stack
                printer.left
                printer.lineIndent
                (not printer.suffixes.isEmpty)
                (arithmetic)
        | Choice options =>
          match mode with
            | Flat => byComputing
            | Break => rewrite chooseEnough printer total extra indent rest options (arithmetic)
        | _ => byComputing

--| Once `fits`'s budget covers the work list's weight, a larger budget
--| prints the same.
theorem runTotalEnough ∀ (printer: Printer) (total extra fuel: Nat) (stack: List Cmd)
    (enough: stackWeight stack ≤ total):
    printer.run (total + extra) fuel stack = printer.run total fuel stack :=
  match fuel, stack with
    | Succ more, [cmd, ..rest] =>
      let heavier := stepWeight printer total cmd rest
      rewrite stepEnough printer total extra cmd rest enough then
        match stepped: printer.step total cmd rest with
          | (next, stack) => runTotalEnough next total extra more stack (arithmetic)
    | _, _ => cases

--| `print`'s budget, 3 * size + 3, is enough both for the printer's steps
--| and for every `fits` it asks: printing with any larger budgets gives
--| the same text.
theorem printBudgetEnough ∀ (printer: Printer) (doc: Doc) (indent: Nat) (mode: Mode) (extraTotal extraFuel: Nat):
    printer.run (3 * doc.size + 3 + extraTotal) (3 * doc.size + 3 + extraFuel) [Print indent mode doc]
      = printer.run (3 * doc.size + 3) (3 * doc.size + 3) [Print indent mode doc] :=
  let bound := stepsUnderSize doc
  rewrite printStepsEnough printer (3 * doc.size + 3 + extraTotal) extraFuel doc indent mode then
    runTotalEnough printer (3 * doc.size + 3) extraTotal (3 * doc.size + 3) [Print indent mode doc] (arithmetic)

--| A `Line` reached while a trailing comment waits is a line break, in a
--| flat group too: no text follows the comment on its line. With
--| `softLineAfterComment`, the `FillSep` step and `textAfterComment`, this
--| is why every trailing comment ends its line, whatever document the
--| engine prints.
theorem lineAfterComment ∀ (printer: Printer) (total indent: Nat) (mode: Mode) (rest: List Cmd)
    (waiting: printer.suffixes.isEmpty = False):
    printer.printDoc total indent mode Line rest = (printer.newline indent, rest) :=
  match mode with
    | Flat => rewrite waiting
    | Break => byComputing

theorem softLineAfterComment ∀ (printer: Printer) (total indent: Nat) (mode: Mode) (rest: List Cmd)
    (waiting: printer.suffixes.isEmpty = False):
    printer.printDoc total indent mode SoftLine rest = (printer.newline indent, rest) :=
  match mode with
    | Flat => rewrite waiting
    | Break => byComputing

--| The next item of a broken `Fill` starts a new line while a trailing
--| comment waits.
theorem fillSepAfterComment ∀ (printer: Printer) (total indent: Nat) (item: Doc) (rest: List Cmd)
    (waiting: printer.suffixes.isEmpty = False):
    printer.step total (FillSep indent item) rest = (printer.newline indent, [Print indent Break item, ..rest]) :=
  rewrite waiting

--| Text reached while a trailing comment waits starts a new line first (a
--| comment break), at least 2 deeper than the line it breaks; spaces there
--| are dropped. So no text ever follows a trailing comment on its line, in
--| any document.
theorem textAfterComment ∀ (printer: Printer) (indent: Nat) (text: Text) (width: Nat)
    (nonEmpty: text.isEmpty = False)
    (waiting: printer.suffixes.isEmpty = False)
    (notSpaces: text.all (char => char == ' ') = False):
    printer.write indent text width = (printer.newline (printer.continuation indent)).put text width :=
  rewrite nonEmpty, waiting, notSpaces

theorem spacesAfterComment ∀ (printer: Printer) (indent: Nat) (text: Text) (width: Nat)
    (nonEmpty: text.isEmpty = False)
    (waiting: printer.suffixes.isEmpty = False)
    (spaces: text.all (char => char == ' ') = True):
    printer.write indent text width = printer :=
  rewrite nonEmpty, waiting, spaces

--| An instance: a space after a waiting comment is dropped.
theorem spacesAfterCommentExample: ({ Printer.start 80 | suffixes = ["-- c"] }).write 0 " " 1
      = { Printer.start 80 | suffixes = ["-- c"] } :=
  spacesAfterComment { Printer.start 80 | suffixes = ["-- c"] } 0 " " 1 byComputing byComputing byComputing

--| A comment break is deeper than the line it breaks.
theorem continuationDeeper ∀ (printer: Printer) (indent: Nat): printer.lineIndent + 2 ≤ printer.continuation indent :=
  Nat.leMaxRight indent (printer.lineIndent + 2)
