-- expect-error: E-CASES
-- `cases` doesn't split inside `Int`'s own arithmetic (SW-937): the
-- `OfNat`/`NegSucc` cases `+` and `-` are stuck on are left to `omega`, so
-- the open case is `command = Up units`, not `Int.subNatNatFrom …`, and the
-- goal is shown in `+`, `-` and `.toInt`. (`Up` should be `-units.toInt`.)

type Command =
  | Forward (units: Nat)
  | Up (units: Nat)

def Command.down: Command → Int
  | Forward units => 0
  | Up units => units.toInt

theorem upAfter (depth: Int) (command: Command): depth + command.down = depth - (match command with | Forward u => 0 | Up u => u.toInt) := cases
