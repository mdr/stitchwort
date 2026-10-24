-- expect-error: E-INSTANCE-NONE
-- Inside a definition abstract over `e`, the result type of `f` is
-- `CompIn e Nat`, stuck on the rigid `e`. It might be `Nat` (the empty row)
-- or `Comp op res Nat` (a row with abilities), and the resolver doesn't
-- guess between `instNat` and `instComp`: there is no instance for the goal
-- as it stands. At a concrete row it resolves
-- (accept/interfaces-comp-in.sw). SW-406, external review of the row design.
import Std (Effect)

interface Label (a: Type) =
  { label: Text }

instance Label.instNat: Label Nat :=
  { label = "nat" }

instance Label.instComp: Label (Effect.Comp op res a) :=
  { label = "comp" }

def describeResult [a b: Type] [auto d: Label b] (f: a -> b): Text := Label.label [a := b]

def abstractOne (f: () -> {e} Nat): Text := describeResult f
