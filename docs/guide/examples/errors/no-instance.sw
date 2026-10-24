type Rule = { name: Text, applies: Nat -> Bool }

def sameRule (a: Rule) (b: Rule): Bool := a == b
