-- Declaration order doesn't matter (docs/proposals/interfaces.md §5.6 rule
-- 4): the uses come first here, then the instances, then the interfaces
-- and the type. Everything else is checked after the module's instances,
-- and an instance after the one its superclass needs.

test "child" := Pretty.pretty (Base.op [base := Child.base [child := Child.instItem]] MkItem) == "item"
test "list" := Pretty.pretty [MkItem] == "[item]"
test "uses" := describe MkItem == "item"

def describe [auto Pretty a] (x: a): Text := Pretty.pretty x

instance Child.instItem: Child Item :=
  { law = x => rfl }

instance Pretty.instList [auto p: Pretty a]: Pretty (List a) :=
  { pretty = xs => "[" ++ Text.join ',' (xs.map Pretty.pretty) ++ "]" }

instance Item.instPretty: Pretty Item :=
  { pretty = i => "item" }

instance Item.instBase: Base Item :=
  { op = i => MkItem }

interface Child (a: Type) =
  { base: Base a
  , law: (x: a) -> base.op (base.op x) = base.op x
  }

interface Base (a: Type) =
  { op: a -> a }

interface Pretty (a: Type) =
  { pretty: a -> Text }

type Item =
  | MkItem
