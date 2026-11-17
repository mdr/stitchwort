-- A second `Closing`, a proposition. The error is at this definition only,
-- not at each use of the name in either file.
namespace N

def Closing (n: Nat): Prop := n = n

theorem closingRefl ∀ (n: Nat): Closing n := byComputing

theorem closingTwice ∀ (n: Nat): Closing n ∧ Closing n := (closingRefl n, closingRefl n)
