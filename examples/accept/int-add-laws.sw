-- Laws for integer addition, and `==` on `Ordering`.

theorem negPlusSelf (a : Int) : a + Int.neg a = Int.OfNat 0 := Int.addNeg a

theorem threeWay (a : Int) (b : Int) (c : Int) : (a + b) + c = a + (b + c) := Int.addAssoc a b c

theorem swap (a : Int) (b : Int) : a + b = b + a := Int.addComm a b

theorem negOfSum (a : Int) (b : Int) : Int.neg (a + b) = Int.neg a + Int.neg b := Int.negAdd a b

theorem selfCancels (a : Int) : Int.sub a a = Int.OfNat 0 := Int.subSelf a

theorem orderingEq : (Ordering.Less == Ordering.Less) = True := rfl

theorem orderingNe : (Ordering.Less == Ordering.Greater) = False := rfl

theorem compareIs : (Int.compare (Int.NegSucc 1) (Int.OfNat 2) == Ordering.Less) = True := rfl
