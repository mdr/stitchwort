--| The printer's budgets are enough. `print` gives the printer 3 steps per
--| node of the document, and 3 more, and gives every `fits` it asks the
--| same budget. Every printer step takes a command off its work list or
--| replaces it by commands that weigh less (`Doc.steps`), so the work list
--| runs out first; and what `fits` can read, the node it measures and the
--| work list after it, never weighs more than the work list did at the
--| start (`Cmd.weight`), so `fits` never runs out either, where it would
--| answer "fits" without looking. Any larger budget prints the same text.

import Doc (..)
import Doc.Proofs (..)

--| The steps the printer can still take on `doc`, at most: a step on a
--| node replaces it by its parts, which weigh less.
def Doc.steps: Doc → Nat
  | Nest _ inner => 1 + inner.steps
  | Align inner => 1 + inner.steps
  | AlignInset inner => 1 + inner.steps
  | Displaced inner => 1 + inner.steps
  | Group inner _ => 1 + inner.steps
  | NarrowGroup _ inner _ => 1 + inner.steps
  | IdGroup _ inner _ => 1 + inner.steps
  | IfBroken _ broken flat => 1 + broken.steps + flat.steps
  | Flatten inner => 1 + inner.steps
  | OneLineBelow inner => 2 + inner.steps
  | Concat docs => 1 + stepsOf docs
  | Fill items => 1 + stepsOf items + items.length
  | Choice options => 2 + stepsOf options
  | _ => 1

--| The steps the printer can still take on the docs, added up.
def Doc.Proofs.stepsOf: List Doc → Nat
  | [] => 0
  | [doc, ..docs] => doc.steps + stepsOf docs

--| The steps the printer can still take on a command.
def Doc.Cmd.cost: Cmd → Nat
  | Print _ _ doc => doc.steps
  | FillSep _ item => item.steps + 1

--| The steps the printer can still take on a work list.
def Doc.Proofs.stackCost: List Cmd → Nat
  | [] => 0
  | [cmd, ..rest] => cmd.cost + stackCost rest

--| Every doc takes at least one step.
theorem Doc.Proofs.stepsPositive ∀ (doc: Doc): 1 ≤ doc.steps := match doc with
  | Nest more inner => arithmetic
  | Align inner => arithmetic
  | AlignInset inner => arithmetic
  | Displaced inner => arithmetic
  | Group inner hard => arithmetic
  | NarrowGroup max inner hard => arithmetic
  | IdGroup id inner hard => arithmetic
  | IfBroken id broken flat => arithmetic
  | Flatten inner => arithmetic
  | OneLineBelow inner => arithmetic
  | Concat docs => arithmetic
  | Fill items => arithmetic
  | Choice options => arithmetic
  | _ => arithmetic

--| The cost of two work lists put together is the sum of their costs.
theorem Doc.Proofs.stackCostAppend ∀ (front back: List Cmd):
    stackCost (front ++ back) = stackCost front + stackCost back :=
  match front with
    | [] => byComputing
    | [cmd, ..rest] => rewrite stackCostAppend rest back then arithmetic

--| Printing each of the docs costs the docs' steps.
theorem Doc.Proofs.costPrints ∀ (indent: Nat) (mode: Mode) (docs: List Doc):
    stackCost (docs.map (Print indent mode)) = stepsOf docs :=
  match docs with
    | [] => byComputing
    | [doc, ..rest] => rewrite costPrints indent mode rest

--| The separators before the items of a fill cost their items' steps.
theorem Doc.Proofs.costFillSeps ∀ (indent: Nat) (items: List Doc):
    stackCost (items.map (FillSep indent)) = stepsOf items + items.length :=
  match items with
    | [] => byComputing
    | [item, ..rest] => rewrite costFillSeps indent rest then arithmetic

--| Putting a `Line` between the items adds at most one step each.
theorem Doc.Proofs.joinLinesSteps ∀ (items: List Doc): stepsOf (Doc.joinLines items) ≤ stepsOf items + items.length :=
  match items with
    | [] => arithmetic
    | [only] => arithmetic
    | [item, next, ..rest] =>
      let tail := joinLinesSteps [next, ..rest]
      arithmetic

--| The first option of a choice takes no more steps than all the options and
--| one.
theorem Doc.Proofs.headOrSteps ∀ (options: List Doc): (options.headOr Doc.Nothing).steps ≤ stepsOf options + 1 :=
  match options with
    | [] => arithmetic
    | [option, ..rest] => arithmetic

--| A bound on both branches of an `if` bounds the `if`, in steps.
theorem Doc.Proofs.ifStepsBound ∀ (condition: Bool) (yes no: Doc) (bound: Nat)
    (yesBound: yes.steps ≤ bound)
    (noBound: no.steps ≤ bound):
    (if condition then yes else no).steps ≤ bound :=
  match condition with
    | True => yesBound
    | False => noBound

--| The branch an `IfBroken` takes costs no more steps than both.
theorem Doc.Proofs.pickSteps ∀ (modes: List (Nat, Mode)) (id: Nat) (broken flat: Doc):
    (pickBranch modes id broken flat).steps ≤ broken.steps + flat.steps :=
  ifStepsBound (brokenIn modes id) broken flat _ (arithmetic) (arithmetic)

--| Whatever option a `Choice` takes costs at most the options' steps and one.
theorem Doc.Proofs.chooseSteps ∀ (printer: Printer) (total indent: Nat) (rest: List Cmd) (options: List Doc):
    (printer.choose total indent rest options).steps ≤ stepsOf options + 1 :=
  match options with
    | [] => arithmetic
    | [last] => arithmetic
    | [option, next, ..others] =>
      let later := chooseSteps printer total indent rest [next, ..others]
      ifStepsBound _ option (printer.choose total indent rest [next, ..others]) _ (arithmetic) (arithmetic [later])

--| A bound on the cost of both results of an `if` bounds the `if`'s result.
theorem Doc.Proofs.ifPairBound ∀ (condition: Bool) (yes no: (Printer, List Cmd)) (bound: Nat)
    (yesBound: stackCost yes.snd < bound)
    (noBound: stackCost no.snd < bound):
    stackCost (if condition then yes else no).snd < bound :=
  match condition with
    | True => yesBound
    | False => noBound

--| Every step weighs the work list down.
theorem Doc.Proofs.stepLighter ∀ (printer: Printer) (total: Nat) (cmd: Cmd) (rest: List Cmd):
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
        | Doc.Nothing => arithmetic
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
        | Mark key => arithmetic
        | CloserLine key => arithmetic
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
        | Align inner => arithmetic
        | AlignInset inner => arithmetic
        | Displaced inner => arithmetic
        | OneLineBelow inner => arithmetic
        | Flatten inner => arithmetic
        | Group inner hard => arithmetic
        | NarrowGroup max inner hard => arithmetic
        | IdGroup id inner hard => arithmetic
        | IfBroken id broken flat =>
          let bound := pickSteps printer.modes id broken flat
          arithmetic
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

--| Every command costs at least one step.
theorem Doc.Proofs.costPositive ∀ (cmd: Cmd): 1 ≤ cmd.cost := match cmd with
  | Print indent mode doc => stepsPositive doc
  | FillSep indent item => arithmetic

--| Once the fuel covers the work list's weight, more fuel prints the same:
--| the work list runs out first.
theorem Doc.Proofs.runFuelEnough ∀ (printer: Printer) (total fuel extra: Nat) (stack: List Cmd)
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

--| Every doc has at least one node.
theorem Doc.Proofs.sizePositive ∀ (doc: Doc): 1 ≤ doc.size := match doc with
  | Nest more inner => arithmetic
  | Align inner => arithmetic
  | AlignInset inner => arithmetic
  | Displaced inner => arithmetic
  | Group inner hard => arithmetic
  | NarrowGroup max inner hard => arithmetic
  | IdGroup id inner hard => arithmetic
  | IfBroken id broken flat => arithmetic
  | Flatten inner => arithmetic
  | OneLineBelow inner => arithmetic
  | Concat docs => arithmetic
  | Fill items => arithmetic
  | Choice options => arithmetic
  | _ => arithmetic

--| A list of docs has no more docs than nodes.
theorem Doc.Proofs.lengthUnderSizes ∀ (docs: List Doc): docs.length ≤ Doc.sizes docs := match docs with
  | [] => arithmetic
  | [doc, ..rest] =>
    let head := sizePositive doc
    let tail := lengthUnderSizes rest
    arithmetic

--| A doc takes at most two steps for each of its nodes.
theorem Doc.Proofs.stepsUnderSize ∀ (doc: Doc): doc.steps ≤ 2 * doc.size := match doc with
  | Nest more inner =>
    let inside := stepsUnderSize inner
    arithmetic
  | Group inner hard =>
    let inside := stepsUnderSize inner
    arithmetic
  | NarrowGroup max inner hard =>
    let inside := stepsUnderSize inner
    arithmetic
  | IdGroup id inner hard =>
    let inside := stepsUnderSize inner
    arithmetic
  | Align inner =>
    let inside := stepsUnderSize inner
    arithmetic
  | AlignInset inner =>
    let inside := stepsUnderSize inner
    arithmetic
  | Displaced inner =>
    let inside := stepsUnderSize inner
    arithmetic
  | IfBroken id broken flat =>
    let one := stepsUnderSize broken
    let other := stepsUnderSize flat
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
  | Doc.Nothing => arithmetic
  | BreakParent => arithmetic
  | Chunk text width => arithmetic
  | Closing text => arithmetic
  | Line => arithmetic
  | SoftLine => arithmetic
  | HardLine => arithmetic
  | LineStart => arithmetic
  | LineStartHere => arithmetic
  | Mark key => arithmetic
  | CloserLine key => arithmetic
  | Blank => arithmetic
  | LineSuffix comment => arithmetic

--| A list of docs takes at most two steps for each of its nodes.
theorem Doc.Proofs.stepsOfUnderSizes ∀ (docs: List Doc): stepsOf docs ≤ 2 * Doc.sizes docs := match docs with
  | [] => arithmetic
  | [doc, ..rest] =>
    let head := stepsUnderSize doc
    let tail := stepsOfUnderSizes rest
    arithmetic

--| `print`'s step budget, three steps per node and three more, is enough:
--| the printer runs out of work before it runs out of steps, so any larger
--| budget prints the same.
theorem Doc.Proofs.printStepsEnough ∀ (printer: Printer) (total extra: Nat) (doc: Doc) (indent: Nat) (mode: Mode):
    printer.run total (3 * doc.size + 3 + extra) [Print indent mode doc]
      = printer.run total (3 * doc.size + 3) [Print indent mode doc] :=
  let bound := stepsUnderSize doc
  runFuelEnough printer total (3 * doc.size + 3) extra [Print indent mode doc] (arithmetic)

--| The steps `fits` can take measuring `stack`.
def Doc.Proofs.pairSteps: List (Nat, Mode, Doc) → Nat
  | [] => 0
  | [(_, _, doc), ..stack] => doc.steps + pairSteps stack

--| The steps `fits` can take reading on into the work list, up to the
--| first fill separator, where it stops.
def Doc.Proofs.restNeed: List Cmd → Nat
  | [Print _ _ doc, ..others] => 1 + doc.steps + restNeed others
  | _ => 0

--| The steps `fits` can take measuring `stack`, then reading on into the work
--| list `rest`.
def Doc.Proofs.fitsNeed (stack: List (Nat, Mode, Doc)) (rest: List Cmd): Nat := pairSteps stack + restNeed rest

--| Measuring docs at one indentation and mode costs their steps, then the rest
--| of the stack.
theorem Doc.Proofs.pairStepsMap ∀ (indent: Nat) (mode: Mode) (docs: List Doc) (stack: List (Nat, Mode, Doc)):
    pairSteps (docs.map (inner => (indent, mode, inner)) ++ stack) = stepsOf docs + pairSteps stack :=
  match docs with
    | [] => byComputing
    | [doc, ..rest] => rewrite pairStepsMap indent mode rest stack then arithmetic

--| The last option of a choice takes no more steps than all the options.
theorem Doc.Proofs.lastSteps ∀ (options: List Doc) (option: Doc)
    (picked: options.last = Some option):
    option.steps ≤ stepsOf options :=
  match options with
    | [only] => rewrite <- Option.someInjective picked then arithmetic
    | [first, second, ..others] =>
      let later := lastSteps [second, ..others] option picked
      arithmetic

--| The first option of a choice takes no more steps than all the options.
theorem Doc.Proofs.headSteps ∀ (options: List Doc) (option: Doc)
    (picked: options.head = Some option):
    option.steps ≤ stepsOf options :=
  match options with | [first, ..others] => rewrite <- Option.someInjective picked then arithmetic

--| With fuel for every step it could take, `fits` gives the same answer
--| as with more: it never stops for want of fuel, where it would answer
--| "fits" without looking.
theorem Doc.Proofs.fitsFromEnough ∀ (fuel extra width: Nat) (modes: List (Nat, Mode)) (stack: List (Nat, Mode, Doc))
    (rest: List Cmd) (left lineIndent: Nat) (suffix: Trailing)
    (enough: fitsNeed stack rest ≤ fuel):
    fitsFrom (fuel + extra) width modes stack rest left lineIndent suffix
      = fitsFrom fuel width modes stack rest left lineIndent suffix :=
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
              rewrite fitsFromEnough more extra width modes
                [(indent, mode, doc)]
                others
                left
                lineIndent
                suffix
                (arithmetic)
        | [(indent, mode, doc), ..stack] =>
          let same := (at to: Nat) (waits: Trailing) (fewer: fitsNeed stack rest ≤ more) =>
            fitsFromEnough more extra width modes stack rest at to waits fewer
          match doc with
            | Doc.Nothing => rewrite same left lineIndent suffix (arithmetic)
            | Blank => rewrite same left lineIndent suffix (arithmetic)
            | Mark key => rewrite same left lineIndent suffix (arithmetic)
            | LineSuffix comment => rewrite same left lineIndent suffix.noted (arithmetic)
            | BreakParent => rewrite same left lineIndent suffix (arithmetic)
            | Chunk text textWidth =>
              match suffix with
                | Clear => rewrite same (left - textWidth) lineIndent Clear (arithmetic)
                | Pending held flatBreak =>
                  match spaces: text.all (char => char == ' ') with
                    | True => rewrite same left lineIndent (Pending (held + textWidth) flatBreak) (arithmetic)
                    | False =>
                      let broken := Nat.max indent (lineIndent + 2)
                      rewrite same (width - broken - textWidth) broken Clear (arithmetic)
            | Closing text =>
              match suffix with
                | Clear => rewrite same (left - text.length) lineIndent Clear (arithmetic)
                | Pending held flatBreak =>
                  rewrite same (left - held - text.length) lineIndent (Pending 0 flatBreak) (arithmetic)
            | Line =>
              match suffix with
                | Clear => rewrite same (left - 1) lineIndent Clear (arithmetic)
                | Pending held _ => rewrite same left lineIndent (Pending held True) (arithmetic)
            | SoftLine =>
              match suffix with
                | Clear => rewrite same left lineIndent Clear (arithmetic)
                | Pending held _ => rewrite same left lineIndent (Pending held True) (arithmetic)
            | HardLine => byComputing
            | LineStart => byComputing
            | LineStartHere => byComputing
            | CloserLine key => byComputing
            | Nest extraIndent inner =>
              rewrite fitsFromEnough more extra width modes
                [(indent + extraIndent, mode, inner), ..stack]
                rest
                left
                lineIndent
                suffix
                (arithmetic)
            | Flatten inner =>
              rewrite fitsFromEnough more extra width modes
                [(indent, Flat, inner), ..stack]
                rest
                left
                lineIndent
                suffix
                (arithmetic)
            | Group inner hard =>
              let measured := if hard then Break else mode
              rewrite fitsFromEnough more extra width modes
                [(indent, measured, inner), ..stack]
                rest
                left
                lineIndent
                suffix
                (arithmetic)
            | NarrowGroup max inner hard =>
              let measured := if hard then Break else mode
              rewrite fitsFromEnough more extra width modes
                [(indent, measured, inner), ..stack]
                rest
                left
                lineIndent
                suffix
                (arithmetic)
            | Align inner =>
              rewrite fitsFromEnough more extra width modes
                [(indent, mode, inner), ..stack]
                rest
                left
                lineIndent
                suffix
                (arithmetic)
            | AlignInset inner =>
              rewrite fitsFromEnough more extra width modes
                [(indent, mode, inner), ..stack]
                rest
                left
                lineIndent
                suffix
                (arithmetic)
            | Displaced inner =>
              rewrite fitsFromEnough more extra width modes
                [(indent, mode, inner), ..stack]
                rest
                left
                lineIndent
                suffix
                (arithmetic)
            | IdGroup id inner hard =>
              let measured := if hard then Break else mode
              rewrite fitsFromEnough more extra width modes
                [(indent, measured, inner), ..stack]
                rest
                left
                lineIndent
                suffix
                (arithmetic)
            | IfBroken id broken flat =>
              let picked := pickBranch modes id broken flat
              let bound := pickSteps modes id broken flat
              rewrite fitsFromEnough more extra width modes
                [(indent, mode, picked), ..stack]
                rest
                left
                lineIndent
                suffix
                (arithmetic)
            | Concat docs =>
              let laid := pairStepsMap indent mode docs stack
              rewrite fitsFromEnough more extra width modes
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
                  rewrite fitsFromEnough more extra width modes
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
                      rewrite fitsFromEnough more extra width modes
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
                      rewrite fitsFromEnough more extra width modes
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
                      rewrite fitsFromEnough more extra width modes
                        [(indent, Break, option), ..stack]
                        rest
                        left
                        lineIndent
                        suffix
                        (arithmetic)

--| What the work list can still cost `fits`, all calls together: a
--| command's steps, and one more step for each node, which reading it out
--| of the work list costs.
def Doc.Cmd.weight: Cmd → Nat
  | Print _ _ doc => doc.steps + doc.size
  | FillSep _ item => item.steps + 1 + item.size

--| The most the work list can cost `fits`, all calls together.
def Doc.Proofs.stackWeight: List Cmd → Nat
  | [] => 0
  | [cmd, ..rest] => cmd.weight + stackWeight rest

--| The weight of two work lists put together is the sum of their weights.
theorem Doc.Proofs.stackWeightAppend ∀ (front back: List Cmd):
    stackWeight (front ++ back) = stackWeight front + stackWeight back :=
  match front with
    | [] => byComputing
    | [cmd, ..rest] => rewrite stackWeightAppend rest back then arithmetic

--| Printing each of the docs weighs their sizes.
theorem Doc.Proofs.weightPrints ∀ (indent: Nat) (mode: Mode) (docs: List Doc):
    stackWeight (docs.map (Print indent mode)) = stepsOf docs + Doc.sizes docs :=
  match docs with
    | [] => byComputing
    | [doc, ..rest] => rewrite weightPrints indent mode rest then arithmetic

--| The separators before the items of a fill weigh their items' sizes.
theorem Doc.Proofs.weightFillSeps ∀ (indent: Nat) (items: List Doc):
    stackWeight (items.map (FillSep indent)) = stepsOf items + items.length + Doc.sizes items :=
  match items with
    | [] => byComputing
    | [item, ..rest] => rewrite weightFillSeps indent rest then arithmetic

--| Putting a `Line` between the items adds at most one node each.
theorem Doc.Proofs.joinLinesSizes ∀ (items: List Doc):
    Doc.sizes (Doc.joinLines items) ≤ Doc.sizes items + items.length :=
  match items with
    | [] => arithmetic
    | [only] => arithmetic
    | [item, next, ..rest] =>
      let tail := joinLinesSizes [next, ..rest]
      arithmetic

--| The first option of a choice has no more nodes than all the options and one.
theorem Doc.Proofs.headOrSize ∀ (options: List Doc): (options.headOr Doc.Nothing).size ≤ Doc.sizes options + 1 :=
  match options with
    | [] => arithmetic
    | [option, ..rest] => arithmetic

--| A bound on both branches of an `if` bounds the `if`, in nodes.
theorem Doc.Proofs.ifBothBound ∀ (condition: Bool) (yes no: Doc) (bound: Nat)
    (yesBound: yes.steps + yes.size ≤ bound)
    (noBound: no.steps + no.size ≤ bound):
    (if condition then yes else no).steps + (if condition then yes else no).size ≤ bound :=
  match condition with
    | True => yesBound
    | False => noBound

--| The branch an `IfBroken` takes weighs no more than both.
theorem Doc.Proofs.pickWeight ∀ (modes: List (Nat, Mode)) (id: Nat) (broken flat: Doc):
    (pickBranch modes id broken flat).steps + (pickBranch modes id broken flat).size
      ≤ broken.steps + flat.steps + broken.size + flat.size :=
  ifBothBound (brokenIn modes id) broken flat _ (arithmetic) (arithmetic)

--| Whatever option a `Choice` takes weighs at most the options' sizes and one.
theorem Doc.Proofs.chooseWeight ∀ (printer: Printer) (total indent: Nat) (rest: List Cmd) (options: List Doc):
    (printer.choose total indent rest options).steps + (printer.choose total indent rest options).size
      ≤ stepsOf options + Doc.sizes options + 2 :=
  match options with
    | [] => arithmetic
    | [last] => arithmetic
    | [option, next, ..others] =>
      let later := chooseWeight printer total indent rest [next, ..others]
      ifBothBound _ option (printer.choose total indent rest [next, ..others]) _ (arithmetic) (arithmetic [later])

--| A bound on the weight of both results of an `if` bounds the `if`'s result.
theorem Doc.Proofs.ifPairWeight ∀ (condition: Bool) (yes no: (Printer, List Cmd)) (bound: Nat)
    (yesBound: stackWeight yes.snd ≤ bound)
    (noBound: stackWeight no.snd ≤ bound):
    stackWeight (if condition then yes else no).snd ≤ bound :=
  match condition with
    | True => yesBound
    | False => noBound

--| No step makes the work list heavier for `fits`.
theorem Doc.Proofs.stepWeight ∀ (printer: Printer) (total: Nat) (cmd: Cmd) (rest: List Cmd):
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
        | Doc.Nothing => arithmetic
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
        | Mark key => arithmetic
        | CloserLine key => arithmetic
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
        | Align inner => arithmetic
        | AlignInset inner => arithmetic
        | Displaced inner => arithmetic
        | OneLineBelow inner => arithmetic
        | Flatten inner => arithmetic
        | Group inner hard => arithmetic
        | NarrowGroup max inner hard => arithmetic
        | IdGroup id inner hard => arithmetic
        | IfBroken id broken flat =>
          let bound := pickWeight printer.modes id broken flat
          arithmetic
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

--| What `fits` can read into a work list is within its weight.
theorem Doc.Proofs.restNeedUnder ∀ (rest: List Cmd): restNeed rest ≤ stackWeight rest := match rest with
  | [] => arithmetic
  | [FillSep indent item, ..others] => arithmetic
  | [Print indent mode doc, ..others] =>
    let positive := sizePositive doc
    let tail := restNeedUnder others
    arithmetic

--| With `fits`'s budget covering the work list's weight, a `Choice` takes the
--| same option as with a larger budget.
theorem Doc.Proofs.chooseEnough ∀ (printer: Printer) (total extra indent: Nat) (rest: List Cmd) (options: List Doc)
    (enough: stepsOf options + restNeed rest ≤ total):
    printer.choose (total + extra) indent rest options = printer.choose total indent rest options :=
  match options with
    | [option, next, ..others] =>
      let later := chooseEnough printer total extra indent rest [next, ..others] (arithmetic)
      match option with
        | OneLineBelow inner =>
          rewrite fitsFromEnough total extra printer.width printer.modes
                [(indent + 2, Flat, inner)]
                []
                (printer.width - indent - 2)
                (indent + 2)
                Clear
                (arithmetic),
              later
        | _ =>
          rewrite fitsFromEnough total extra printer.width printer.modes
                [(indent, Break, option)]
                rest
                printer.left
                printer.lineIndent
                printer.waiting
                (arithmetic),
              later
    | _ => cases

--| With `fits`'s budget covering the work list's weight, a step takes the
--| same choices as with a larger budget.
theorem Doc.Proofs.stepEnough ∀ (printer: Printer) (total extra: Nat) (cmd: Cmd) (rest: List Cmd)
    (enough: cmd.weight + stackWeight rest ≤ total):
    printer.step (total + extra) cmd rest = printer.step total cmd rest :=
  let under := restNeedUnder rest
  match cmd with
    | FillSep indent item =>
      rewrite fitsFromEnough total extra printer.width printer.modes
        [(indent, Flat, item)]
        rest
        (printer.left - 1)
        printer.lineIndent
        Clear
        (arithmetic)
    | Print indent mode doc =>
      match doc with
        | Group inner hard =>
          rewrite fitsFromEnough total extra printer.width printer.modes
            [(indent, Flat, inner)]
            rest
            printer.left
            printer.lineIndent
            printer.waiting
            (arithmetic)
        | NarrowGroup max inner hard =>
          rewrite fitsFromEnough total extra printer.width printer.modes
            [(indent, Flat, inner)]
            rest
            (Nat.min printer.left (max - printer.owed.getOrElse printer.column))
            printer.lineIndent
            printer.waiting
            (arithmetic)
        | IdGroup id inner hard =>
          rewrite fitsFromEnough total extra printer.width printer.modes
            [(indent, Flat, inner)]
            rest
            printer.left
            printer.lineIndent
            printer.waiting
            (arithmetic)
        | Fill items =>
          match items with
            | [] => byComputing
            | [first, ..others] =>
              let stack := others.map (FillSep indent) ++ rest
              let laid := stackWeightAppend (others.map (FillSep indent)) rest
              let seps := weightFillSeps indent others
              let need := restNeedUnder stack
              rewrite fitsFromEnough total extra printer.width printer.modes
                [(indent, Flat, first)]
                stack
                printer.left
                printer.lineIndent
                printer.waiting
                (arithmetic)
        | Choice options =>
          match mode with
            | Flat => byComputing
            | Break => rewrite chooseEnough printer total extra indent rest options (arithmetic)
        | _ => byComputing

--| Once `fits`'s budget covers the work list's weight, a larger budget
--| prints the same.
theorem Doc.Proofs.runTotalEnough ∀ (printer: Printer) (total extra fuel: Nat) (stack: List Cmd)
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
theorem Doc.Proofs.printBudgetEnough ∀ (printer: Printer) (doc: Doc) (indent: Nat)
    (mode: Mode) (extraTotal extraFuel: Nat):
    printer.run (3 * doc.size + 3 + extraTotal) (3 * doc.size + 3 + extraFuel) [Print indent mode doc]
      = printer.run (3 * doc.size + 3) (3 * doc.size + 3) [Print indent mode doc] :=
  let bound := stepsUnderSize doc
  rewrite printStepsEnough printer (3 * doc.size + 3 + extraTotal) extraFuel doc indent mode then
    runTotalEnough printer (3 * doc.size + 3) extraTotal (3 * doc.size + 3) [Print indent mode doc] (arithmetic)

--| A flat `Line` reached while a trailing comment waits holds a space,
--| written only if a closer follows: with
--| `softLineAfterComment`, `textAfterComment` and `closePut`,
--| this is why every trailing comment ends its line, whatever document
--| the engine prints.
theorem Doc.Proofs.lineAfterComment ∀ (printer: Printer) (total indent: Nat) (rest: List Cmd)
    (waiting: printer.suffixes.isEmpty = False):
    printer.printDoc total indent Flat Line rest = ({ printer | heldSpaces = printer.heldSpaces + 1 }, rest) :=
  rewrite waiting

--| A flat `SoftLine` is nothing, while a trailing comment waits too.
theorem Doc.Proofs.softLineAfterComment ∀ (printer: Printer) (total indent: Nat) (rest: List Cmd):
    printer.printDoc total indent Flat SoftLine rest = (printer, rest) :=
  byComputing

--| The next item of a broken `Fill` starts a new line while a trailing
--| comment waits.
theorem Doc.Proofs.fillSepAfterComment ∀ (printer: Printer) (total indent: Nat) (item: Doc) (rest: List Cmd)
    (waiting: printer.suffixes.isEmpty = False):
    printer.step total (FillSep indent item) rest = (printer.newline indent, [Print indent Break item, ..rest]) :=
  rewrite waiting

--| Text reached while a trailing comment waits starts a new line first
--| (a comment break), at least 2 deeper than the line it
--| breaks. So no text ever follows a trailing comment on its line, in any
--| document.
theorem Doc.Proofs.textAfterComment ∀ (printer: Printer) (indent: Nat) (text: Text) (width: Nat)
    (nonEmpty: text.isEmpty = False)
    (waiting: printer.suffixes.isEmpty = False)
    (notSpaces: text.all (char => char == ' ') = False):
    printer.write indent text width = (printer.newline (printer.continuation indent)).put text width :=
  rewrite nonEmpty, waiting, notSpaces

--| Spaces written while a trailing comment waits are held.
theorem Doc.Proofs.spacesAfterComment ∀ (printer: Printer) (indent: Nat) (text: Text) (width: Nat)
    (nonEmpty: text.isEmpty = False)
    (waiting: printer.suffixes.isEmpty = False)
    (spaces: text.all (char => char == ' ') = True):
    printer.write indent text width = { printer | heldSpaces = printer.heldSpaces + text.length } :=
  rewrite nonEmpty, waiting, spaces

--| An instance: a space after a waiting comment is held.
theorem Doc.Proofs.spacesAfterCommentExample: ({ Printer.start 80 | suffixes = ["-- c"] }).write 0 " " 1
      = { Printer.start 80 | suffixes = ["-- c"], heldSpaces = 1 } :=
  spacesAfterComment { Printer.start 80 | suffixes = ["-- c"] } 0 " " 1 byComputing byComputing byComputing

--| An instance: `Both ( ) -- c`.
theorem Doc.Proofs.closeAfterCommentExample: (Doc.print
      (Doc.concat [Doc.text "Both (", LineSuffix "-- c", Doc.text " ", Closing ")"])
      120
      == "Both ( ) -- c")
      = True :=
  byComputing

--| A comment break is deeper than the line it breaks.
theorem Doc.Proofs.continuationDeeper ∀ (printer: Printer) (indent: Nat):
    printer.lineIndent + 2 ≤ printer.continuation indent :=
  Nat.leMaxRight indent (printer.lineIndent + 2)
