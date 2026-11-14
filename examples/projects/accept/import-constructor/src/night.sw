-- Naming a constructor alone imports just that constructor: `Move` and
-- `Forward` aren't imported by it.
namespace Night

import Turns (Counterclockwise)

test "a constructor imported alone" := Counterclockwise == Counterclockwise
