-- expect-error: E-TYPE-MISMATCH
-- The arm's body is checked once for each alternative, and `amount` is a
-- `Text` in the second: the error names that alternative and the type
-- `amount` has there.
type Payment = | Cash (amount: Nat) | Cheque (amount: Text)

def total (payment: Payment): Nat := match payment with | Cash amount | Cheque amount => amount + 1
