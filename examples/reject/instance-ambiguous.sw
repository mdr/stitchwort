-- expect-error: E-INSTANCE-AMBIGUOUS
-- Two different dictionaries for `Pretty a` are in scope, and nothing says
-- they're the same (docs/proposals/interfaces.md §5.5), so the compiler
-- won't choose. instance-ambiguous-swapped.sw has them the other way round,
-- with the same error. The accepted neighbour passes one by name:
-- `sideBySide` in examples/accept/interfaces-by-name.sw.

interface Pretty (a: Type) =
  { pretty: a → Text }

def both [auto first: Pretty a] [auto second: Pretty a] (x: a): Text :=
  Pretty.pretty x
