--| The printer's budgets are enough. `print` gives the printer 3 steps per
--| node of the document, and 3 more, and gives every `fits` it asks the
--| same budget. Every printer step takes a command off its work list or
--| replaces it by commands that weigh less (`Doc.steps`), so the work list
--| runs out first; and what `fits` can read, the node it measures and the
--| work list after it, never weighs more than the work list did at the
--| start (`Cmd.weight`), so `fits` never runs out either, where it would
--| answer "fits" without looking. Any larger budget prints the same text.

namespace Toy.Doc.Proofs
import Toy.Doc (..)
import Std (List, Nat, Option, Text, Void)

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
  | Nest more inner => omega
  | Group inner hard => omega
  | Flatten inner => omega
  | OneLineBelow inner => omega
  | Concat docs => omega
  | Fill items => omega
  | Choice options => omega
  | _ => omega

theorem stackCostAppend ∀ (front back: List Cmd): stackCost (front ++ back) = stackCost front + stackCost back :=
  match front with
    | [] => rfl
    | [cmd, ..rest] => rewrite stackCostAppend rest back in omega

theorem costPrints ∀ (indent: Nat) (mode: Mode) (docs: List Doc):
    stackCost (docs.map (Print indent mode)) = stepsOf docs :=
  match docs with
    | [] => rfl
    | [doc, ..rest] => rewrite costPrints indent mode rest in rfl

theorem costFillSeps ∀ (indent: Nat) (items: List Doc):
    stackCost (items.map (FillSep indent)) = stepsOf items + items.length :=
  match items with
    | [] => rfl
    | [item, ..rest] => rewrite costFillSeps indent rest in omega

theorem joinLinesSteps ∀ (items: List Doc): stepsOf (Doc.joinLines items) ≤ stepsOf items + items.length :=
  match items with
    | [] => omega
    | [only] => omega
    | [item, next, ..rest] =>
      let tail := joinLinesSteps [next, ..rest]
      omega

theorem headOrSteps ∀ (options: List Doc): (options.headOr Empty).steps ≤ stepsOf options + 1 := match options with
  | [] => omega
  | [option, ..rest] => omega

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
    | [] => omega
    | [last] => omega
    | [option, next, ..others] =>
      let later := chooseSteps printer total indent rest [next, ..others]
      ifStepsBound _ option (printer.choose total indent rest [next, ..others]) _ (omega) (omega [later])

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
        (printer.write " " 1, [Print indent Flat item, ..rest])
        (printer.newline indent, [Print indent Break item, ..rest])
        (item.steps + 1 + stackCost rest)
        (omega)
        (omega)
    | Print indent mode doc =>
      match doc with
        | Empty => omega
        | BreakParent => omega
        | Chunk text width => omega
        | Line =>
          ifPairBound _ (printer.write " " 1, rest) (printer.newline indent, rest) (1 + stackCost rest) (omega) (omega)
        | SoftLine => ifPairBound _ (printer, rest) (printer.newline indent, rest) (1 + stackCost rest) (omega) (omega)
        | HardLine => omega
        | Blank => omega
        | LineSuffix comment => omega
        | Nest more inner => omega
        | OneLineBelow inner => omega
        | Flatten inner => omega
        | Group inner hard => omega
        | Concat docs =>
          rewrite stackCostAppend (docs.map (Print indent mode)) rest, costPrints indent mode docs in omega
        | Fill items =>
          match items with
            | [] => omega
            | [first, ..others] =>
              match mode with
                | Flat =>
                  let joinedLines := Doc.joinLines [first, ..others]
                  let bound := joinLinesSteps [first, ..others]
                  rewrite stackCostAppend (joinedLines.map (Print indent Flat)) rest,
                      costPrints indent Flat joinedLines in
                    omega
                | Break =>
                  rewrite stackCostAppend (others.map (FillSep indent)) rest, costFillSeps indent others in omega
        | Choice options =>
          match mode with
            | Flat =>
              let bound := headOrSteps options
              omega
            | Break =>
              let bound := chooseSteps printer total indent rest options
              omega

theorem costPositive ∀ (cmd: Cmd): 1 ≤ cmd.cost := match cmd with
  | Print indent mode doc => stepsPositive doc
  | FillSep indent item => omega

--| Once the fuel covers the work list's weight, more fuel prints the same:
--| the work list runs out first.
theorem runFuelEnough ∀ (printer: Printer) (total fuel extra: Nat) (stack: List Cmd)
    (enough: stackCost stack ≤ fuel):
    printer.run total (fuel + extra) stack = printer.run total fuel stack :=
  match fuel, stack with
    | Zero, [] =>
      match extra with
        | Zero => rfl
        | Succ more => rfl
    | Succ more, [] => rfl
    | Zero, [cmd, ..rest] =>
      let positive := costPositive cmd
      Void.exfalso (omega)
    | Succ more, [cmd, ..rest] =>
      let lighter := stepLighter printer total cmd rest
      match stepped: printer.step total cmd rest with
        | (next, stack) => runFuelEnough next total more extra stack (omega)

theorem sizePositive ∀ (doc: Doc): 1 ≤ doc.size := match doc with
  | Nest more inner => omega
  | Group inner hard => omega
  | Flatten inner => omega
  | OneLineBelow inner => omega
  | Concat docs => omega
  | Fill items => omega
  | Choice options => omega
  | _ => omega

theorem lengthUnderSizes ∀ (docs: List Doc): docs.length ≤ Doc.sizes docs := match docs with
  | [] => omega
  | [doc, ..rest] =>
    let head := sizePositive doc
    let tail := lengthUnderSizes rest
    omega

theorem stepsUnderSize ∀ (doc: Doc): doc.steps ≤ 2 * doc.size := match doc with
  | Nest more inner =>
    let inside := stepsUnderSize inner
    omega
  | Group inner hard =>
    let inside := stepsUnderSize inner
    omega
  | Flatten inner =>
    let inside := stepsUnderSize inner
    omega
  | OneLineBelow inner =>
    let inside := stepsUnderSize inner
    omega
  | Concat docs =>
    let inside := stepsOfUnderSizes docs
    omega
  | Fill items =>
    let inside := stepsOfUnderSizes items
    let count := lengthUnderSizes items
    omega
  | Choice options =>
    let inside := stepsOfUnderSizes options
    omega
  | Empty => omega
  | BreakParent => omega
  | Chunk text width => omega
  | Line => omega
  | SoftLine => omega
  | HardLine => omega
  | Blank => omega
  | LineSuffix comment => omega

theorem stepsOfUnderSizes ∀ (docs: List Doc): stepsOf docs ≤ 2 * Doc.sizes docs := match docs with
  | [] => omega
  | [doc, ..rest] =>
    let head := stepsUnderSize doc
    let tail := stepsOfUnderSizes rest
    omega

--| `print`'s step budget, three steps per node and three more, is enough:
--| the printer runs out of work before it runs out of steps, so any larger
--| budget prints the same.
theorem printStepsEnough ∀ (printer: Printer) (total extra: Nat) (doc: Doc) (indent: Nat) (mode: Mode):
    printer.run total (3 * doc.size + 3 + extra) [Print indent mode doc]
      = printer.run total (3 * doc.size + 3) [Print indent mode doc] :=
  let bound := stepsUnderSize doc
  runFuelEnough printer total (3 * doc.size + 3) extra [Print indent mode doc] (omega)

--| The steps `fits` can take measuring `stack`.
def pairSteps: List (Mode, Doc) → Nat
  | [] => 0
  | [(_, doc), ..stack] => doc.steps + pairSteps stack

--| The steps `fits` can take reading on into the work list, up to the
--| first fill separator, where it stops.
def restNeed: List Cmd → Nat
  | [Print _ _ doc, ..others] => 1 + doc.steps + restNeed others
  | _ => 0

def fitsNeed (stack: List (Mode, Doc)) (rest: List Cmd): Nat := pairSteps stack + restNeed rest

theorem pairStepsMap ∀ (mode: Mode) (docs: List Doc) (stack: List (Mode, Doc)):
    pairSteps (docs.map (inner => (mode, inner)) ++ stack) = stepsOf docs + pairSteps stack :=
  match docs with
    | [] => rfl
    | [doc, ..rest] => rewrite pairStepsMap mode rest stack in omega

theorem lastSteps ∀ (options: List Doc) (option: Doc)
    (picked: options.last = Some option):
    option.steps ≤ stepsOf options :=
  match options with
    | [only] => rewrite <- Option.someInjective picked in omega
    | [first, second, ..others] =>
      let later := lastSteps [second, ..others] option picked
      omega

theorem headSteps ∀ (options: List Doc) (option: Doc)
    (picked: options.head = Some option):
    option.steps ≤ stepsOf options :=
  match options with | [first, ..others] => rewrite <- Option.someInjective picked in omega

--| With fuel for every step it could take, `fits` gives the same answer
--| as with more: it never stops for want of fuel, where it would answer
--| "fits" without looking.
theorem fitsFromEnough ∀ (fuel extra: Nat) (stack: List (Mode, Doc)) (rest: List Cmd) (left: Nat) (suffix: Bool)
    (enough: fitsNeed stack rest ≤ fuel):
    fitsFrom (fuel + extra) stack rest left suffix = fitsFrom fuel stack rest left suffix :=
  match fuel with
    | Zero =>
      match stack, rest with
        | [], [] =>
          match extra with
            | Zero => rfl
            | Succ more => rfl
        | [], [FillSep indent item, ..others] =>
          match extra with
            | Zero => rfl
            | Succ more => rfl
        | [(mode, doc), ..stack], _ =>
          let positive := stepsPositive doc
          Void.exfalso (omega)
    | Succ more =>
      match stack with
        | [] =>
          match rest with
            | [] => rfl
            | [FillSep indent item, ..others] => rfl
            | [Print indent mode doc, ..others] =>
              rewrite fitsFromEnough more extra [(mode, doc)] others left suffix (omega) in rfl
        | [(mode, doc), ..stack] =>
          match doc with
            | Empty => rewrite fitsFromEnough more extra stack rest left suffix (omega) in rfl
            | Blank => rewrite fitsFromEnough more extra stack rest left suffix (omega) in rfl
            | LineSuffix comment => rewrite fitsFromEnough more extra stack rest left True (omega) in rfl
            | BreakParent => rewrite fitsFromEnough more extra stack rest left suffix (omega) in rfl
            | Chunk text width => rewrite fitsFromEnough more extra stack rest (left - width) suffix (omega) in rfl
            | Line => rewrite fitsFromEnough more extra stack rest (left - 1) suffix (omega) in rfl
            | SoftLine => rewrite fitsFromEnough more extra stack rest left suffix (omega) in rfl
            | HardLine => rfl
            | Nest indent inner =>
              rewrite fitsFromEnough more extra [(mode, inner), ..stack] rest left suffix (omega) in rfl
            | Flatten inner =>
              rewrite fitsFromEnough more extra [(Flat, inner), ..stack] rest left suffix (omega) in rfl
            | Group inner hard =>
              let measured := if hard then Break else mode
              rewrite fitsFromEnough more extra [(measured, inner), ..stack] rest left suffix (omega) in rfl
            | Concat docs =>
              let laid := pairStepsMap mode docs stack
              rewrite fitsFromEnough more extra (docs.map (inner => (mode, inner)) ++ stack) rest left suffix (omega) in
                rfl
            | Fill items =>
              match mode with
                | Flat =>
                  let joinedLines := Doc.joinLines items
                  let laid := pairStepsMap Flat joinedLines stack
                  let bound := joinLinesSteps items
                  rewrite fitsFromEnough more extra
                        (joinedLines.map (inner => (Flat, inner)) ++ stack)
                        rest
                        left
                        suffix
                        (omega) in
                    rfl
                | Break =>
                  match items with
                    | [] => rfl
                    | [first, ..others] =>
                      rewrite fitsFromEnough more extra [(Flat, first)] [] left False (omega) in rfl
            | OneLineBelow inner => rfl
            | Choice options =>
              match mode with
                | Flat =>
                  match picked: options.head with
                    | None => rewrite fitsFromEnough more extra stack rest left suffix (omega) in rfl
                    | Some option =>
                      let bound := headSteps options option picked
                      rewrite fitsFromEnough more extra [(Flat, option), ..stack] rest left suffix (omega) in rfl
                | Break =>
                  match picked: options.last with
                    | None => rewrite fitsFromEnough more extra stack rest left suffix (omega) in rfl
                    | Some option =>
                      let bound := lastSteps options option picked
                      rewrite fitsFromEnough more extra [(Break, option), ..stack] rest left suffix (omega) in rfl

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
    | [] => rfl
    | [cmd, ..rest] => rewrite stackWeightAppend rest back in omega

theorem weightPrints ∀ (indent: Nat) (mode: Mode) (docs: List Doc):
    stackWeight (docs.map (Print indent mode)) = stepsOf docs + Doc.sizes docs :=
  match docs with
    | [] => rfl
    | [doc, ..rest] => rewrite weightPrints indent mode rest in omega

theorem weightFillSeps ∀ (indent: Nat) (items: List Doc):
    stackWeight (items.map (FillSep indent)) = stepsOf items + items.length + Doc.sizes items :=
  match items with
    | [] => rfl
    | [item, ..rest] => rewrite weightFillSeps indent rest in omega

theorem joinLinesSizes ∀ (items: List Doc): Doc.sizes (Doc.joinLines items) ≤ Doc.sizes items + items.length :=
  match items with
    | [] => omega
    | [only] => omega
    | [item, next, ..rest] =>
      let tail := joinLinesSizes [next, ..rest]
      omega

theorem headOrSize ∀ (options: List Doc): (options.headOr Empty).size ≤ Doc.sizes options + 1 := match options with
  | [] => omega
  | [option, ..rest] => omega

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
    | [] => omega
    | [last] => omega
    | [option, next, ..others] =>
      let later := chooseWeight printer total indent rest [next, ..others]
      ifBothBound _ option (printer.choose total indent rest [next, ..others]) _ (omega) (omega [later])

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
        (printer.write " " 1, [Print indent Flat item, ..rest])
        (printer.newline indent, [Print indent Break item, ..rest])
        (item.steps + 1 + item.size + stackWeight rest)
        (omega)
        (omega)
    | Print indent mode doc =>
      match doc with
        | Empty => omega
        | BreakParent => omega
        | Chunk text width => omega
        | Line =>
          ifPairWeight _
            (printer.write " " 1, rest)
            (printer.newline indent, rest)
            (2 + stackWeight rest)
            (omega)
            (omega)
        | SoftLine =>
          ifPairWeight _ (printer, rest) (printer.newline indent, rest) (2 + stackWeight rest) (omega) (omega)
        | HardLine => omega
        | Blank => omega
        | LineSuffix comment => omega
        | Nest more inner => omega
        | OneLineBelow inner => omega
        | Flatten inner => omega
        | Group inner hard => omega
        | Concat docs =>
          rewrite stackWeightAppend (docs.map (Print indent mode)) rest, weightPrints indent mode docs in omega
        | Fill items =>
          match items with
            | [] => omega
            | [first, ..others] =>
              match mode with
                | Flat =>
                  let joinedLines := Doc.joinLines [first, ..others]
                  let bound := joinLinesSteps [first, ..others]
                  let sized := joinLinesSizes [first, ..others]
                  let count := lengthUnderSizes [first, ..others]
                  rewrite stackWeightAppend (joinedLines.map (Print indent Flat)) rest,
                      weightPrints indent Flat joinedLines in
                    omega
                | Break =>
                  let count := lengthUnderSizes others
                  rewrite stackWeightAppend (others.map (FillSep indent)) rest, weightFillSeps indent others in omega
        | Choice options =>
          match mode with
            | Flat =>
              let bound := headOrSteps options
              let sized := headOrSize options
              omega
            | Break =>
              let bound := chooseWeight printer total indent rest options
              omega

theorem restNeedUnder ∀ (rest: List Cmd): restNeed rest ≤ stackWeight rest := match rest with
  | [] => omega
  | [FillSep indent item, ..others] => omega
  | [Print indent mode doc, ..others] =>
    let positive := sizePositive doc
    let tail := restNeedUnder others
    omega

theorem chooseEnough ∀ (printer: Printer) (total extra indent: Nat) (rest: List Cmd) (options: List Doc)
    (enough: stepsOf options + restNeed rest ≤ total):
    printer.choose (total + extra) indent rest options = printer.choose total indent rest options :=
  match options with
    | [] => rfl
    | [last] => rfl
    | [option, next, ..others] =>
      let later := chooseEnough printer total extra indent rest [next, ..others] (omega)
      match option with
        | OneLineBelow inner =>
          rewrite fitsFromEnough total extra [(Flat, inner)] [] (printer.width - indent - 2) False (omega) in
            rewrite later in rfl
        | _ =>
          rewrite fitsFromEnough total extra
                [(Break, option)]
                rest
                printer.left
                (not printer.suffixes.isEmpty)
                (omega) in
            rewrite later in rfl

--| With `fits`'s budget covering the work list's weight, a step takes the
--| same choices as with a larger budget.
theorem stepEnough ∀ (printer: Printer) (total extra: Nat) (cmd: Cmd) (rest: List Cmd)
    (enough: cmd.weight + stackWeight rest ≤ total):
    printer.step (total + extra) cmd rest = printer.step total cmd rest :=
  let under := restNeedUnder rest
  match cmd with
    | FillSep indent item =>
      rewrite fitsFromEnough total extra [(Flat, item)] rest (printer.left - 1) False (omega) in rfl
    | Print indent mode doc =>
      match doc with
        | Group inner hard =>
          rewrite fitsFromEnough total extra [(Flat, inner)] rest printer.left (not printer.suffixes.isEmpty) (omega) in
            rfl
        | Fill items =>
          match items with
            | [] => rfl
            | [first, ..others] =>
              let stack := others.map (FillSep indent) ++ rest
              let laid := stackWeightAppend (others.map (FillSep indent)) rest
              let seps := weightFillSeps indent others
              let need := restNeedUnder stack
              rewrite fitsFromEnough total extra
                    [(Flat, first)]
                    stack
                    printer.left
                    (not printer.suffixes.isEmpty)
                    (omega) in
                rfl
        | Choice options =>
          match mode with
            | Flat => rfl
            | Break => rewrite chooseEnough printer total extra indent rest options (omega) in rfl
        | _ => rfl

--| Once `fits`'s budget covers the work list's weight, a larger budget
--| prints the same.
theorem runTotalEnough ∀ (printer: Printer) (total extra fuel: Nat) (stack: List Cmd)
    (enough: stackWeight stack ≤ total):
    printer.run (total + extra) fuel stack = printer.run total fuel stack :=
  match fuel, stack with
    | Zero, _ => rfl
    | Succ more, [] => rfl
    | Succ more, [cmd, ..rest] =>
      let heavier := stepWeight printer total cmd rest
      rewrite stepEnough printer total extra cmd rest enough in
        match stepped: printer.step total cmd rest with
          | (next, stack) => runTotalEnough next total extra more stack (omega)

--| `print`'s budget, 3 * size + 3, is enough both for the printer's steps
--| and for every `fits` it asks: printing with any larger budgets gives
--| the same text.
theorem printBudgetEnough ∀ (printer: Printer) (doc: Doc) (indent: Nat) (mode: Mode) (extraTotal extraFuel: Nat):
    printer.run (3 * doc.size + 3 + extraTotal) (3 * doc.size + 3 + extraFuel) [Print indent mode doc]
      = printer.run (3 * doc.size + 3) (3 * doc.size + 3) [Print indent mode doc] :=
  let bound := stepsUnderSize doc
  rewrite printStepsEnough printer (3 * doc.size + 3 + extraTotal) extraFuel doc indent mode in
    runTotalEnough printer (3 * doc.size + 3) extraTotal (3 * doc.size + 3) [Print indent mode doc] (omega)
