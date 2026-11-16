namespace User

import Lib (one, pick)

def total: Nat := one + pick 1

theorem totalIsThree: total = 3 := rfl
