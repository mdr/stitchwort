-- A `def …: Type` alias, used through a section.
def Bank: Type := List Nat

def Bank.maxJoltage (bank: Bank) (count: Nat): Nat := bank.take count |> .sum

def solve (banks: List Bank): Nat := banks |> .sumBy (.maxJoltage 2)
