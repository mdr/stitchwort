-- expect-error: E-NONEXHAUSTIVE
-- Numbers alone never cover every case: there's always another number.
def statusText: Nat → Text
  | 200 => "OK"
  | 404 => "Not Found"
