-- `Always property c`: every result `c` can finish with satisfies `property`,
-- whatever its operations answer. It is about the computation alone, so a
-- handler that answers and resumes needs one lemma, by induction on
-- `AlwaysTree` with `match reify`, to carry it to the handler's result.
-- `Always` computes, so a proof takes one argument per operation performed;
-- `alwaysBind` steps over a part that is stuck, such as a loop over a list of
-- unknown length.

import Effect (Comp, bind)
import Effect.Comp (Done, Call)
import Effect.AlwaysTreeOf (AlwaysDone, AlwaysCall)

-- Every result of `computation` satisfies `property`.
def Effect.Always [op: Type] [res: op → Type] [a: Type] (property: a → Prop): Comp op res a → Prop
  | Done x => property x
  | Call o rest => (y: res o) → Effect.Always property (rest y)

-- Every result satisfies a property that always holds.
theorem Effect.alwaysUnit [op: Type] [res: op → Type] [a: Type]: (computation: Comp op res a) → Effect.Always (x => Unit) computation
  | Done x => Trivial
  | Call o rest => y => Effect.alwaysUnit (rest y)

-- Sequencing: if every result of `computation` satisfies `first`, and `next`
-- of any value satisfying `first` always gives results satisfying
-- `property`, so does running one and then the other.
theorem Effect.alwaysBind [op: Type] [res: op → Type] [a b: Type] (first: a → Prop) (property: b → Prop) (next: a → Comp op res b):
    (computation: Comp op res a) → Effect.Always first computation → ((x: a) → first x → Effect.Always property (next x)) →
    Effect.Always property (bind computation next)
  | Done x, holds, after => after x holds
  | Call o rest, holds, after => y => Effect.alwaysBind first property next (rest y) (holds y) after

-- `Always` as data: a proof by induction on it may recurse on the proof for
-- the rest of the computation, which is smaller. A handler's lemma recurses
-- this way.
type Effect.AlwaysTreeOf (op: Type) (res: op → Type) (a: Type) (property: a → Prop): Comp op res a → Prop =
  | AlwaysDone (x: a) (holds: property x): Effect.AlwaysTreeOf op res a property (Done x)
  | AlwaysCall (o: op) (rest: res o → Comp op res a) (holds: (y: res o) → Effect.AlwaysTreeOf op res a property (rest y)):
    Effect.AlwaysTreeOf op res a property (Call o rest)

-- `AlwaysTreeOf`, with the signature found from the computation.
def Effect.AlwaysTree [op: Type] [res: op → Type] [a: Type] (property: a → Prop) (computation: Comp op res a): Prop :=
  Effect.AlwaysTreeOf op res a property computation

theorem Effect.Always.tree [op: Type] [res: op → Type] [a: Type] (property: a → Prop):
    (computation: Comp op res a) → Effect.Always property computation → Effect.AlwaysTree property computation
  | Done x, holds => AlwaysDone x holds
  | Call o rest, holds => AlwaysCall o rest (y => Effect.Always.tree property (rest y) (holds y))

-- The result of a finished computation satisfies the property.
theorem Effect.AlwaysTree.done [op: Type] [res: op → Type] [a: Type] (property: a → Prop) (x: a):
    Effect.AlwaysTree property (Done x: Comp op res a) → property x
  | AlwaysDone _ holds => holds
