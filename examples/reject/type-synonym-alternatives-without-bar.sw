-- expect-error: E-PARSE
-- `type T = A | B` needs the leading `|`: `type T = | A | B`.
type T = A | B
