-- expect-error: E-UNKNOWN-FIELD
-- `.joinWith` on a `List Text` looks in `List`, which has none. The message
-- names only that namespace, and points to `Text.joinWith`, which takes the
-- list first.
import Std (List, Nat, Text)

def shown (blocks: List Nat): Text := blocks.map (block => "${block}") |> .joinWith ""
