--| Slice 1's third top theorem (D3687, Matt, 19 Nov 2026): the driver formats every source of slice 1's grammar.
--| `formatKeepsProgram1` and `formatIdempotent1` (`Fmt.TopStatements`) say what holds of a source the driver
--| accepts; this says which sources those are. Slice 1 is done when all three are proved.
--|
--| The statement is fixed. `inGrammar1` is the design's grammar (`Fmt.Grammar1`), not a test taken from the
--| driver, so the theorem is proved by making `formatWithin1` accept more, never by narrowing the grammar or adding a
--| condition here. A case leaves the grammar only by a decision of Matt's that names the later slice it moves to.

namespace Fmt.Accepts1
import Std (Bool, Result, Text)
import Fmt.Grammar1 (inGrammar1)
import Fmt.Driver1 (formatWithin1)

--| Every source in slice 1's grammar is formatted: whatever its layout and wherever its comments are, the driver
--| refuses none of it.
--|
--| Open, and false of the driver as it stands on 19 Nov 2026, which refuses a qualified name, an exponent, an
--| upper-case definition name, the name `auto`, a last comma that starts its line, and a declaration that doesn't
--| print on one line (`Fmt.Tests.MustAccept1` has a failing test for each; docs/reviews/SW-4120-grammar1.md).
theorem formatAccepts1 ∀ (source: Text)
    (inGrammar: inGrammar1 source = True):
    ∃ (out: Text) => formatWithin1 source = Ok out :=
  ?
