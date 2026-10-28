-- expect-error: E-UNKNOWN-FIELD
-- `digits` is a hand-written `List Nat`, whose type doesn't mention `Code`,
-- so `.numericPart` is looked up in `List` only; the note says why and
-- suggests the full name or an annotation.

type Code = List Nat

def Code.numericPart (code: Code): Nat := code.foldLeft 0 (number digit => 10 * number + digit)

def handWritten (digits: List Nat): Nat := digits.numericPart
