-- expect-error: E-UNKNOWN-NAME
-- Only a whole argument of a type is bound automatically: `highest + 1`
-- is arithmetic on an unknown name, which stays an error, so a misspelt
-- value doesn't silently become a new parameter.
type Dial (highest: Nat) = { position: Nat, inRange: position <= highest }

def bigger (d: Dial (highest + 1)): Nat := d.position
