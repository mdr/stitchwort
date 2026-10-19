namespace Day

import Lib (..)
import Twin (..)

-- Each `Range` has a constructor `R`: ambiguous, not unknown.
test "r" := R == R
