-- expect-error: E-INSTANCE-CONTEXT
-- What an instance asks for must be about the variables of its head
-- (docs/proposals/interfaces.md §5.2), a smaller type, so finding instances
-- always ends. This one asks for the very thing it is. The accepted
-- neighbour, `Pretty.instList` asking for `Pretty a`, is in
-- examples/accept/interfaces.sw.

interface Pretty (a: Type) =
  { pretty: a → Text }

instance Pretty.instList [auto p: Pretty (List a)]: Pretty (List a) :=
  { pretty = xs => Pretty.pretty xs }
