-- expect-error: E-TYPE-MISMATCH
-- An operand with a literal inside doesn't decide the type before a minus
-- sign does (D732): with nothing else to go on, this is an `Int` group.
-- Write `(-(Float.abs 1.5): Float)` for the operand.
import Std (Float)

def same: Bool := -(Float.abs 1.5) == -(Float.abs 2.5)
