import Std (IO)

def total (prices: List Nat): Nat :=
  IO.print "adding up ${prices.length} prices"
  prices.sum
