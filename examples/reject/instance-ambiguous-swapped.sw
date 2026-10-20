-- expect-error: E-INSTANCE-AMBIGUOUS
-- instance-ambiguous.sw with the dictionaries in scope the other way round:
-- the same error, naming them in the same order. Which candidates there are
-- doesn't depend on the order they were bound in.

interface Pretty (a: Type) =
  { pretty: a -> Text }

def both [auto second: Pretty a] [auto first: Pretty a] (x: a): Text :=
  Pretty.pretty x
