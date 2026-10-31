namespace Shop.Other

import Shop (Spec)

def Spec.mine: Nat := 3

test "mine" := Spec.mine == 3
