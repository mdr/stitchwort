-- expect-warning: W-REDUNDANT
-- An arm after an unguarded one that matches everything it does is never
-- chosen, as without a guard. A guarded arm after a guarded one is not
-- flagged: the conditions may differ (docs/proposals/pattern-guards.md §5).

def twice: Nat → Nat
  | n if n > 3 => n
  | n if n > 3 => n + 1
  | n => n
  | m if m > 7 => m

-- The hidden last arm of `match some` is reached through a guard.
def kept: Nat → Option Nat := match some | x if x > 0 => x
