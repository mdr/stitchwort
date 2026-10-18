-- Unit parameters: unused var, wildcard, and a used var.

main : () -> {IO} ()
main u = print "hi"

mainWild : () -> {IO} ()
mainWild _ = print "hi"

keep : () -> Pair () Nat
keep u = MkPair u 3

twoUnits : () -> () -> Nat
twoUnits u v = 1
