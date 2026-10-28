-- expect-error: E-PARSE
-- A type's parameter is a binder with its type, `(k: Type)`: a bare name
-- after the type's name is an error whose note shows the bracketed form.

type Position = { row: Nat, column: Nat }

type Keypad k = { place: k → Position, gap: Position }
