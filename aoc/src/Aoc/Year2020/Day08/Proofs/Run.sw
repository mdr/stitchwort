--| A run of the program's `Code.runFrom` is a run of the spec's `Runs`:
--| for any code that holds a program's instructions, the positions it
--| executes are distinct, and it stops where its outcome says.

namespace Aoc.Year2020.Day08.Proofs
import Aoc.Year2020.Day08 (..)
import Aoc.Year2020.Day08.Spec (Executes, Runs, Step, instructionAt)
import Std (Bool, DecEq, Eq, Int, List, Map, Nat, Option, Set, Void)

--| `code` holds `program`'s instructions, by position.
def Holds (code: Code) (program: Program): Prop :=
  code.length = program.instructions.length
    ∧ (∀ (position: Nat) => code.byPosition.get position = program.instructions.get position)

--| What a run that executed the instructions at `executed` and stopped at
--| `last` says about how it ended.
def Ended (program: Program) (executed: List Int) (last: State): (outcome: Outcome) → Prop
  | Loops accumulator => last.next ∈ executed ∧ accumulator = last.accumulator
  | Terminates accumulator => last.next = program.instructions.length.toInt ∧ accumulator = last.accumulator
  | JumpsAway accumulator => Unit

--| `unvisited` holds the positions in the code that `done` hasn't run.
def Unvisited (length: Nat) (done: List Int) (unvisited: Set Nat): Prop :=
  ∀ (position: Nat) => unvisited.contains position = True ↔ (position < length ∧ position.toInt ∉ done)

theorem nextIs ∀ (next: Int) (position: Nat) (found: next.toNatChecked = Some position): next = position.toInt :=
  match next with | OfNat n => Eq.cong OfNat (Option.someInjective found)

theorem executeSteps ∀ (program: Program) (state: State) (instruction: Instruction)
    (at: instructionAt program state.next = Some instruction):
    Step program state (instruction.execute state) :=
  Witness instruction
    (Both at
      (match instruction with
        | { operation = Acc, argument } => Both rfl rfl
        | { operation = Jmp, argument } => Both rfl rfl
        | { operation = Nop, argument } => Both rfl rfl))

theorem unvisitedRemove ∀ (length: Nat) (done: List Int) (unvisited: Set Nat)
    (left: Unvisited length done unvisited) (position: Nat):
    Unvisited length (done ++ [position.toInt]) (unvisited.remove position) :=
  other =>
    match d: other == position with
      | True =>
        rewrite d.read, Set.containsRemove unvisited position in
          {
            forward = never => cases,
            backward = (Both below out) =>
              Void.exfalso (out (List.memAppendRight position.toInt done [position.toInt] (Inl rfl)))
          }
      | False =>
        let differ: other ≠ position := same => d.read same
        rewrite Set.containsRemoveOther unvisited position other differ in
          {
            forward = held =>
              let (Both below out) := (left other).forward held
              Both below (m =>
                match List.memAppend other.toInt done [position.toInt] m with
                  | Inl inDone => out inDone
                  | Inr (Inl same) => differ (Int.ofNatInjective other position (Eq.sym same))
                  | Inr (Inr none) => none),
            backward = (Both below out) =>
              (left other).backward (Both below (m => out (List.memAppendLeft other.toInt done [position.toInt] m)))
          }

theorem runFromRuns ∀ (program: Program) (code: Code)
    (holds: Holds code program)
    (unvisited: Set Nat) (state: State) (done: List Int)
    (left: Unvisited code.length done unvisited)
    (distinct: List.Distinct done):
    ∃ (positions: List Int) => ∃ (last: State) => Runs program state positions last
      ∧ List.Distinct (done ++ positions)
      ∧ Ended program (done ++ positions) last (code.runFrom unvisited state)
    decreasing unvisited.size
:=
  let stopped: List.Distinct (done ++ []) := rewrite List.appendNil done in distinct
  rewrite Code.runFrom.unfold code unvisited state in
    match e: state.next.toNatChecked with
      | None => Witness [] (Witness state (Both rfl (Both stopped ())))
      | Some position =>
        let here: state.next = position.toInt := nextIs state.next position e
        match g: code.byPosition.get position with
          | None =>
            match t: position == code.length with
              | True =>
                Witness []
                  (Witness state (Both rfl (Both stopped (Both (rewrite here, t.read, And.left holds in rfl) rfl))))
              | False => Witness [] (Witness state (Both rfl (Both stopped ())))
          | Some instruction =>
            let listed: program.instructions.get position = Some instruction := rewrite <- And.right holds position in g
            let below: position < code.length :=
              rewrite And.left holds in List.getSomeLt program.instructions position instruction listed
            match c: unvisited.contains position with
              | True =>
                let out: position.toInt ∉ done := And.right ((left position).forward c)
                let at: instructionAt program state.next = Some instruction := rewrite e in listed
                let ih :=
                  runFromRuns program code holds
                    (unvisited.remove position)
                    (instruction.execute state)
                    (done ++ [position.toInt])
                    (unvisitedRemove code.length done unvisited left position)
                    (List.distinctSnoc done position.toInt out distinct)
                    [decreasing := omega [
                      Set.sizeRemovePresent unvisited position c,
                      Set.sizePositive unvisited position c
                    ]]
                match ih with
                  | Witness positions (Witness last (Both runs (Both distinctAll ended))) =>
                    Witness
                      [state.next, ..positions]
                      (Witness last
                        (Both
                          (Both rfl
                            (Witness
                              (instruction.execute state)
                              (Both (executeSteps program state instruction at) runs)))
                          (rewrite <- List.appendAssoc done [state.next] positions, here in Both distinctAll ended)))
              | False =>
                let seen: state.next ∈ done :=
                  if m: position.toInt ∈ done then rewrite here in m
                  else Void.exfalso (Bool.falseNotTrue (Eq.trans (Eq.sym c) ((left position).backward (Both below m))))
                Witness [] (Witness state (Both rfl (Both stopped (Both (rewrite List.appendNil done in seen) rfl))))
