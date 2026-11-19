--| The line rule read from a group's tokens (H1 of SW-4121's plan): `hangs` reads tokens only, and in a group that
--| keeps it every closer and comma is inside a bracket, where the parser's line test lets it start a line.

namespace Syntax.ReadBackHungDeep
import Std (Bool, List, Nat, Option)
import Syntax (..)
import Fmt (..)
import Syntax.SettleProofs (tokens)
import Syntax.ReadBackHung (..)

--| Leaves with the same tokens keep the line rule alike: `hangs` reads only their tokens.
theorem hangsTokens ∀ (first second: List Leaf) (same: tokens first = tokens second): hangs first = hangs second := ?

--| In a group that keeps the line rule, every closer and comma item has a bracket open before it.
theorem hungDeep ∀ (group: List Leaf) (hung: hangs group = True): deepAll (items group) = True := ?
