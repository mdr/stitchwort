import Std (Option, SafeNat)

-- `export` makes a function available to JavaScript and TypeScript. See the
-- JavaScript tab for the generated module and its `.d.ts`.
type Profile = { name: Text, nickname: Option Text }

-- An `Option` is `T | undefined` in JS; in a record it is an optional field.
export def displayName (p: Profile): Text := Option.getOrElse p.nickname p.name

-- A `Nat` is a `bigint`. `SafeNat` is a whole number that fits a JS
-- `number`, and `ofNat` says `None` when it doesn't.
export def toNumber (n: Nat): Option SafeNat := SafeNat.ofNat n

-- A numeral can be a `SafeNat` directly; the compiler checks its bound.
def kilobyte: SafeNat := 1024

test "a safe literal" := kilobyte.value == 1024

-- A proof the caller can't give statically becomes a runtime check.
export def percentOf (percent: Nat) (total: Nat): [auto ok: percent <= 100] -> Nat := total * percent / 100
