-- `<` on colours needs `colorOrd`, which has an error: `before` and the
-- test that calls it wait for it, said once, here. `==` uses `Color`'s
-- derived `DecEq` instance, which is fine, so `same` is checked and its
-- test runs.
namespace Day

import Colors (Color, Red, Green)

def before (a: Color) (b: Color): Bool := a < b

def same (a: Color) (b: Color): Bool := a == b

test "same" := same Red Red

test "before" := before Red Green
