-- `()` where a proof of the proposition `Unit` is expected is its one proof,
-- `Trivial`, as it is the unit value where a value of `()` is expected.
import Std (List)

theorem distinctNil: List.Distinct (Nil: List Nat) := ()

theorem unitDirect: Unit := ()

theorem bothUnit: Unit && Unit := Both () ()

def unitValue: () := ()

test "the unit value is still a value" := unitValue == ()
