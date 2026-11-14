-- A `Prop` method after `∧` in a lambda whose parameter's type comes from a
-- later argument: the operand is a proposition, not "a type of data".
import Std (List)

type Slot = { candidates: List Nat }

def Slot.sound (slot: Slot): Prop := slot.candidates = []

def AllSound (slots: List Slot): Prop := List.All (slot => slot.candidates = [] ∧ slot.sound) slots
