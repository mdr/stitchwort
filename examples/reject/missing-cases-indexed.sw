-- expect-error: E-NONEXHAUSTIVE
-- A case that can't happen is left out of the list: `BoolE` can't be an
-- `Expr TInt`, so only `Add` and `If` are missing.
type Tag =
  | TInt
  | TBool

type Expr: Tag → Type =
  | IntE (n: Nat): Expr TInt
  | BoolE (b: Bool): Expr TBool
  | Add (x: Expr TInt) (y: Expr TInt): Expr TInt
  | If (c: Expr TBool) (t: Expr k) (e: Expr k): Expr k

def eval: Expr TInt → Nat
  | IntE n => n
