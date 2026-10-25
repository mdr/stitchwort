-- Instance resolution on the result type of an effect-polymorphic callback
-- (SW-406, external review of the row design). `labelOf f` needs
-- `Label b`, where `b` is the result type of `f`: for `f: () -> {e} Nat`
-- that is `CompIn e Nat`, which is `Nat` at the empty row and
-- `Comp op res Nat` at a row with abilities.
--
-- The rule: once the row is concrete, the type computes and the instance for
-- what it computes to is used. Resolution never guesses the row. Inside a
-- definition abstract over `e`, the goal is stuck and has no instance
-- (`reject/interfaces-comp-in-rigid-row.sw`); a row unknown still undecided
-- is the unifier's business (`CompIn ?e B`: put aside, then defaulted to the
-- empty row, D1123), never the resolver's.
import Std (Effect, Fail)

interface Label (a: Type) =
  { label: Text }

instance Label.instNat: Label Nat :=
  { label = "nat" }

instance Label.instComp: Label (Effect.Comp op res a) :=
  { label = "comp" }

def labelOf [a b: Type] [auto d: Label b] (f: a → b): Text := Label.label [a := b]

-- Nothing else is stuck: a concrete result type.
def pureOne: Text := labelOf ((n: Nat) => n)

-- A concrete row with an ability: the goal is `Label (Comp ... Nat)`.
def failing (f: () → {Fail} Nat): Text := labelOf f

-- A row unknown nothing decides: put aside, then the empty row, so `Label Nat`.
def unknownRow: Text := labelOf (() => 3)

test "concrete result type" := pureOne == "nat"
test "concrete row with an ability" := failing (() => 3) == "comp"
test "unknown row defaults to empty" := unknownRow == "nat"
