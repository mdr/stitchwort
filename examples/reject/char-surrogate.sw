-- expect-error: E-PARSE
-- A surrogate isn't a Unicode scalar value, so it isn't a character.
def bad : Char := '\u{D800}'
