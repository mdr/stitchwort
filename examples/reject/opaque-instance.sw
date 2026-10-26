-- expect-error: E-PARSE
-- An instance is used by taking it apart, which needs its body.
-- (docs/proposals/opaque-definitions.md §6.2.)
import Std (Nat, Show)

type Box = { contents: Nat }

opaque instance Box.instShow: Show Box := { show = box => box.contents.show }
