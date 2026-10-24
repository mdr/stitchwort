-- expect-error: E-ABILITY

import Std (List, Fail, Text)

-- `List.map` takes a callback that may fail, but then the call may fail
-- too, and this function's type says it can't (D1124: a callback with
-- abilities makes the row effectful, even when the result is expected to be a
-- plain list).
def lengths (texts: List Text): List Nat := texts.map Text.toNatOrFail

-- The same where the list is an argument: the call is run first, and
-- `Fail` isn't allowed there either.
def count (texts: List Text): Nat := List.length (texts.map Text.toNatOrFail)
