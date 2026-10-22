-- An alias for a list, with a function in the alias's own namespace.
namespace Shop

def Bank: Type := List Nat

def Bank.total (extra: Nat) (bank: Bank): Nat := extra + bank.sum

-- The same, in the alias's own namespace.
def sameTotalHome: Prop := (bank: Bank) -> bank.total 1 = bank.total 1
