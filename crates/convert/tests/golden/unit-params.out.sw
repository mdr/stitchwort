-- Unit parameters: unused var, wildcard, and a used var.

def main () : {IO} () := print "hi"

def mainWild () : {IO} () := print "hi"

def keep (u : ()) : Pair () Nat := MkPair u 3

def twoUnits () () : Nat := 1
