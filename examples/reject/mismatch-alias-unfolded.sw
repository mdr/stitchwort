-- expect-error: E-TYPE-MISMATCH
-- An alias keeps its name in a message, which can hide the difference: `Vec Bool`
-- says nothing about its element type until unfolded. The message adds
-- "`Vec Bool` is `List Bool`" because the unfolding has the same head as
-- the other side. (Against `Nat`, whose head differs, it says nothing extra.)

def Vec (a: Type): Type := List a

def wrong (xs: List Nat): List Nat := ([] : Vec Bool)
