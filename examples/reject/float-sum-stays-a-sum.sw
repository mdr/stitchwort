-- expect-error: E-REFL
-- A sum of unknown doubles computes to itself, not to `Float.Model`'s bit
-- arithmetic: `Float.add` waits for both doubles' bits, though `Float` has
-- record eta (D2551). So the note shows the sum `span.start + span.length`
-- as a call of `Float.add`, not its bits.
import Std (Float)

type Span = { start: Float, length: Float }

def Span.end (span: Span): Float := span.start + span.length

theorem endCommutes (span: Span): span.end = span.length + span.start := rfl
