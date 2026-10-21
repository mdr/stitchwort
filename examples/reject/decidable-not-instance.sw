-- expect-error: E-AUTO-NONE
-- `if` and `auto` use only decision procedures marked `instance` (D163,
-- docs/proposals/interfaces.md §5.12): this `def` isn't one. The accepted
-- neighbour, `decToken` as an `instance`, is in examples/accept/eqeq-deceq.sw.

type Token: Prop =
  | MkToken

def decToken: Decidable Token := Yes MkToken

test "not found" := if Token then True else False
