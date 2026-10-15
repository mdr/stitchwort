-- expect-error: E-NONEXHAUSTIVE
-- Numbers alone never cover every case: there's always another number.
statusText : Nat -> Text
statusText 200 = "OK"
statusText 404 = "Not Found"
