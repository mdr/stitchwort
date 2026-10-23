-- expect-error: E-EXPORT
-- An `Option` behind a synonym is found when an export reaches the record:
-- unboxed, `None` and `Some { value = None }` would both be `undefined`.
import Std (Option, Text)

type MaybeText = Option Text

@[js.unboxed]
type Nickname = { value: MaybeText }

export def nick (n: Nickname): Text := "x"
