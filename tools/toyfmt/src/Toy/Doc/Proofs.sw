--| The printer's fuel is enough: `print` gives the printer three steps per
--| node of the document (and three more), and every step takes one command
--| off its work list or replaces it by commands of less weight, so the work
--| list runs out first. More fuel would print the same text.

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
