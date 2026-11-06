-- expect-error: E-TYPE-MISMATCH
-- A method returning data after `∧` in a lambda is still not a proposition.
import Std (List)

type Slot = { candidates: List Nat }

def Slot.size (slot: Slot): Nat := 3

def AllSized (slots: List Slot): Prop :=
  List.All (slot => slot.candidates = [] ∧ slot.size) slots
