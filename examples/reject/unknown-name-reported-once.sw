-- expect-error: E-UNKNOWN-NAME
-- A record has no `mk`; one use is one report, however often its declaration
-- is elaborated.

type Passport = { byr: Text, iyr: Text }

def make: Passport := Passport.mk "a" "b"
