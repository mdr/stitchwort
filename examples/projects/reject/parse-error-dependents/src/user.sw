namespace User

import Lib (..)

def total: Nat := one + pick 1

theorem totalIsThree: total = 3 := byComputing
