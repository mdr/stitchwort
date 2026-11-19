-- expect-error: E-TYPE-MISMATCH
-- An error the body makes the same way in every alternative is reported
-- once, saying it is in each of them.
type Payment = | Cash (amount: Nat) | Card (amount: Nat)

def label (payment: Payment): Text := match payment with | Cash amount | Card amount => amount
