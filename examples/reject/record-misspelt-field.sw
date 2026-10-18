-- expect-error: E-UNKNOWN-FIELD
-- `.nmae` isn't a field of `Person`; the message lists the fields.

type Person = { name : Text, age : Nat }

def nameOf (p : Person) : Text := p.nmae
