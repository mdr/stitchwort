--| The two statements `printedSettle` rests on, against stage 1's rule N
--| (spike K1, SW-3825), and the same two over `sample`'s small alphabet.
--| `Fmt.Sketch.Search` tries them natively; `Settled.sw` has what they
--| say and why.

namespace Fmt.Sketch.SettledProofs
import Fmt.Sketch.Settled (..)
import Syntax (Leaf, Lexed)
import Std (Bool, List)

--| Rule N's result is `homed`, whatever the source's layout.
theorem settledHomed ∀ (lexed: Lexed) (choices: List Bool)
    (plainly: plain (lexed.laid False choices).leaves = True):
    homed (lexed.laid False choices).settled.leaves = True :=
  ?

--| Rule N's result, written out again in any layout that starts a line
--| at each closer or bar holding a comment, settles to itself: the same
--| comments on the same tokens. This is `printedSettle` on leaves; the
--| printer's part is that its layout is such a one.
theorem settledAnyLayout ∀ (lexed: Lexed) (choices again: List Bool)
    (plainly: plain (lexed.laid False choices).leaves = True):
    ((lexed.laid False choices).settled.laid True again).settled.bare = (lexed.laid False choices).settled.bare :=
  ?

-- The same over small alphabets.

theorem sampleHomed ∀ (cells: List Cell)
    (plainly: plain (sample cells).leaves = True):
    homed (sample cells).settled.leaves = True :=
  ?

theorem sampleAnyLayout ∀ (cells: List Cell) (again: List Bool)
    (plainly: plain (sample cells).leaves = True):
    ((sample cells).settled.laid True again).settled.bare = (sample cells).settled.bare :=
  ?
