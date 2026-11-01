-- A `type` alias with a function in its namespace.
type Code = List Nat

def Code.numericPart (code: Code): Nat := code.foldLeft 0 (number digit => 10 * number + digit)

-- The lambda's parameter type comes from inference (`List Code`).
def total (codes: List Code): Nat := codes.sumBy (code => code.numericPart)

-- The lambda's parameter is annotated with the alias.
def totalAnnotated (codes: List Code): Nat := codes.sumBy ((code: Code) => code.numericPart)
