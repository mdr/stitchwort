-- expect-error: E-PARSE
-- A surrogate isn't a Unicode scalar value, so it isn't a character.
bad : Char
bad = '\u{D800}'
