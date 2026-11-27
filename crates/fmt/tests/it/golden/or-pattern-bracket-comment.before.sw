-- A comment inside brackets that are an or-pattern alternative stays inside:
-- after the closer it would end the alternative's line, and the next `|`
-- would start a new arm, which the parser rejects (SW-4911).
def f (xs: List Nat): Nat := match xs with | [-- c
] | [_, .._] => 0

-- With `=>` after the brackets, or a plain value, the layout stays as it
-- was: the comment waits for the end of the line after the closer.
def g (xs: List Nat): Nat := match xs with | [-- c
] => 0

def h: List Nat := [-- c
]

-- A comment between a non-empty alternative's item and its closer stays
-- inside too.
def i (xs: List Nat): Nat := match xs with | [1 -- c
] | [_, .._] => 0
