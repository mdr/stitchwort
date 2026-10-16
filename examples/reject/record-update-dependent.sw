-- expect-error: E-RECORD-UPDATE
-- Replacing `items` alone would leave `sorted` about the old list: an update
-- must replace every later field whose type mentions a replaced one. The
-- accepted neighbour, which replaces `ok` too, is `grown` in
-- examples/accept/records.sw.

IsShort : List Nat -> Prop
IsShort xs = length xs <= 2

type Short = { items : List Nat, short : IsShort items }

one : Short
one = { items = [1], short = rfl }

two : Short
two = { one | items = [1, 2, 3] }
