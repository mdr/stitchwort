import Std (Bool, Nat)

def isSmall (n: Nat): Bool := n <= 3

theorem bigWhenNot ∀ (n: Nat) (h: isSmall n = False): 3 < n := h
