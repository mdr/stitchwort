type Rule = { name: Text, applies: Nat → Bool }

def sameRule (a b: Rule): Bool := a == b
