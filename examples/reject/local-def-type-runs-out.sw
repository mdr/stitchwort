-- expect-error: E-PARSE
-- A local definition whose result type is missing at the end of the file is
-- one syntax error, at the gap after its `:`.
theorem t: Unit :=
  def f (s: Nat):
