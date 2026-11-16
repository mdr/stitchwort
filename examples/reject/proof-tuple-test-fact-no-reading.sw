-- expect-error: E-NO-READING
-- A tuple pattern on a test fact is `Both`/`Witness` written shorter; when
-- the fact reads as something that isn't `∧` or `∃`, the message says what
-- it reads as, as the constructor pattern does.
theorem t (a b: Bool) (h: (a && b) = False): a = False := match h with
  | (x, _) => x
