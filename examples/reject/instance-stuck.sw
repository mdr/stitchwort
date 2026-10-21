-- expect-error: E-INSTANCE-STUCK
-- Whether the dictionary in scope, `p: Pretty (List a)`, gives
-- `Pretty (List ?)` depends on what the elements of `[]` are, which nothing
-- says. Resolution never guesses by solving that unknown to make the
-- dictionary fit (docs/proposals/interfaces.md §5.5): it waits, and reports
-- what it waited for.

interface Pretty (a: Type) =
  { pretty: a -> Text }

def shown [auto p: Pretty (List a)] (x: a): Text := Pretty.pretty []
