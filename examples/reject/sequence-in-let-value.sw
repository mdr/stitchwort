-- expect-error: E-TYPE-MISMATCH
-- A `;` straight after a `let`'s value ends the value, so this binds
-- `x := 1` with the body `2; x`, not `x := (1; 2)`: the body's value is
-- `x`, a `Nat`, not the `Text` the signature says. Brackets make a
-- sequence the value: `(let x := (1; "two"); x)`.
import Std (Nat, Text)

def value: Text := (let x := 1; 2; x)
