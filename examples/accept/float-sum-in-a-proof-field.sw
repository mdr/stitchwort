-- A sum of unknown doubles stays `x + y` when computed: `Float.add` waits
-- for both doubles' bits, though `Float` has record eta (D2551). The proof
-- field below is read back under its binder `span`, where `span.end` is
-- `span.start + span.length` on unknowns; computing that further would
-- write out `Float.Model`'s bit arithmetic, far too large to show (SW-1744).
import Std (Float, List)

type Span = { start: Float, length: Float }

def Span.end (span: Span): Float := span.start + span.length

type Timeline = { spans: List Span, forward: List.All (span => Float.leq span.start span.end = True) spans }

def Timeline.empty: Timeline := { spans = [], forward = Trivial }

test "an empty timeline has no spans" := Timeline.empty.spans.length == 0
