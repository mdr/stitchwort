-- expect-error: E-EXPORT
-- A parameter's `Options` may leave out its defaulted fields, so it has an
-- input shape, `OptionsInput`, in the TypeScript declarations: another type
-- at the boundary can't have that name (docs/proposals/named-arguments.md
-- §5.3).
type Options = { size: Nat := 1 }

type OptionsInput = { text: Text }

export def measure (options: Options) (input: OptionsInput): Nat := options.size
