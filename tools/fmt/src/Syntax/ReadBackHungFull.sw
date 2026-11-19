--| What `expr` reads on any lines, one depth at a time (H5 of SW-4121's plan, the block case): given `fullHung` below
--| `depth`, `fullHung` at `depth`. `Syntax.ReadBackHungTop.fullHung` ties the knot by induction on the depth.

namespace Syntax.ReadBackHungFull
import Std (Bool, List, Nat, Option)
import Syntax (..)
import Fmt (..)
import Syntax.ReadBackProofs (..)
import Syntax.ReadBackRuns (..)
import Syntax.ReadBackTree (..)
import Syntax.ReadBackEnds (..)
import Syntax.ReadBackLine (..)
import Syntax.ReadBackHung (..)
import Syntax.ReadBackHungInline (..)

--| A spelt expression at the start of a type, a value or a bracket's item (`state.start`), or after `->`
--| (`state.glue`), whose leaves and what follows keep the line rule, is what `expr` reads: inline where its first item
--| starts no block (`inlineHung`); else a one-line block at that item's column, read by `inlineHung` under the block's
--| modes (`open` from `allow`, `bound` by `boundsBlock`, `BlockAt`'s first clause by `rightOfBound`, its second by
--| `stepInBracket` or `stepAtTop`).
theorem fullHungStep ∀ (depth: Nat) (inner: FullHungBelow depth): FullHungAt depth := ?
