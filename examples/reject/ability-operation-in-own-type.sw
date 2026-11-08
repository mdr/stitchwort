-- expect-error: E-ABILITY
-- An operation's type can't mention an operation of the same ability: they
-- don't exist until every type is checked.
ability State where
  get: () → {State} get
