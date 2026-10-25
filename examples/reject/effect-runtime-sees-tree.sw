-- expect-error: E-PROOF-ONLY
-- A program can't take a computation apart (docs/proposals/proof-reification.md,
-- D1145, stage R2): `Done` and `Call` are for proofs. This helper and the
-- predicate built on it once made `finishedNow (() => failing 0)` false and
-- `finishedNow (() => failing 3)` true at run time.
import Std (Effect, Fail)
import Std.Effect.Comp (Done, Call)

def viewOf [op: Type] [res: op → Type] [a: Type] (t: () → Effect.Comp op res a): Effect.Comp op res a := t ()

def finishedNow [op: Type] [res: op → Type] [a: Type] (t: () → Effect.Comp op res a): Bool :=
  match viewOf t with
    | Done x => True
    | Call o k => False

def failing (n: Nat): {Fail} Nat := if n == 0 then Fail.fail "zero" else n

test "runtime sees the tree" := finishedNow (() => failing 0) == False
