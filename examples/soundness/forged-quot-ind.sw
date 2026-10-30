-- expect-error: E-DUPLICATE
-- Arena `forged-quot-ind`, the eliminator's name: `Quot.ind` can't be
-- redefined either. Neighbour: accept/quot-forms.sw.
def Quot.ind (n: Nat): Nat := n
