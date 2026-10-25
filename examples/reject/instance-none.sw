-- expect-error: E-INSTANCE-NONE
-- No `Pretty` instance for `Item`. The message says where one may be
-- declared, and names a dictionary of the right type that could be passed
-- by name.

interface Pretty (a: Type) =
  { pretty: a → Text }

type Item =
  | MkItem

def plain: Pretty Item := { pretty = i => "item" }

def shown: Text := Pretty.pretty MkItem
