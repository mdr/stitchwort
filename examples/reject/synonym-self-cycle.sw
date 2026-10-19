-- expect-error: E-SYNONYM-CYCLE
-- A synonym that mentions itself, even inside another type, never reaches a type.
type A = List A
