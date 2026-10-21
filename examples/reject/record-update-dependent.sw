-- expect-error: E-RECORD-UPDATE
-- Replacing `items` alone would leave `sorted` about the old list: an update
-- must replace every later field whose type mentions a replaced one. The
-- accepted neighbour, which replaces `ok` too, is `grown` in
-- examples/accept/records.sw.

import Std (List)

def IsShort (xs: List Nat): Prop := List.length xs <= 2

type Short = { items: List Nat, short: IsShort items }

def one: Short := { items = [1], short = rfl }

def two: Short := { one | items = [1, 2, 3] }
