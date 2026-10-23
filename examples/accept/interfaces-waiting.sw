-- Resolution doesn't depend on the order obligations are tried in
-- (docs/proposals/interfaces.md §5.5): a test that depends on an unknown
-- waits, and is tried again once it's known.

import Std (Nat)

interface HasZero (a: Type) =
  { zero: a }

instance HasZero.instNat: HasZero Nat :=
  { zero = 0 }

interface Pretty (a: Type) =
  { pretty: a -> Text }

type W (n: Nat) =
  | MkW

instance W.instPretty: Pretty (W n) :=
  { pretty = w => "global" }

-- The re-review's example: a local dictionary whose type is
-- `Pretty (W 0)` only once its `HasZero Nat` is found.
def makePretty [auto z: HasZero Nat]: Pretty (W (HasZero.zero [hasZero := z])) :=
  { pretty = w => "local" }

-- `HasZero Nat` is found first, then `o` matches `Pretty (W 0)`, and wins
-- over the global instance.
def zeroFirst: Text :=
  let o: Pretty (W (HasZero.zero [hasZero := _])) := makePretty
  Pretty.pretty [a := W 0] MkW

-- `Pretty (W 0)` is tried first. Whether `o` gives it is blocked on the
-- unknown `HasZero Nat`, so it waits, rather than take the global instance;
-- then `o` matches.
def goalFirst: Text :=
  ((o: Pretty (W (HasZero.zero [hasZero := _]))) => Pretty.pretty [a := W 0] MkW) makePretty

def noLocal: Text := Pretty.pretty [a := W 0] MkW

test "zero first" := zeroFirst == "local"
test "goal first" := goalFirst == "local"
test "no local" := noLocal == "global"

-- Two dictionaries in scope, `build ?d1` and `build ?d2`, where `?d1` and
-- `?d2` are found after `Pretty Nat` is first tried: whether they're the
-- same dictionary can't be told until then. Then they're merged, and win
-- over the global instance.
instance Pretty.instNat: Pretty Nat :=
  { pretty = n => "global" }

def build [auto z: HasZero Nat]: Pretty Nat :=
  { pretty = n => if n == HasZero.zero [hasZero := z] then "zero" else "local" }

def same (p: Pretty Nat) (q: Pretty Nat) (e: p = q): Text := ""

def mergedLater: Text :=
  let o1: Pretty Nat := build [z := _]
  let o2: Pretty Nat := build [z := _]
  Pretty.pretty 0 ++ same o1 build rfl ++ same o2 build rfl

-- The same, with `?d1` and `?d2` found first.
def mergedFirst: Text :=
  let o1: Pretty Nat := build
  let o2: Pretty Nat := build
  Pretty.pretty 5

test "merged later" := mergedLater == "zero"
test "merged first" := mergedFirst == "local"

-- A dictionary in a head (`o`, a head variable of `Box.instPretty`) that
-- matching equates with an unknown (`box`'s own `?ord`) isn't a solution:
-- `Pretty (Box Nat ?ord)` waits for `?ord`'s own obligation, then applies.
interface Ordered (a: Type) =
  { less: a -> a -> Bool }

instance Ordered.instNat: Ordered Nat :=
  { less = m n => Nat.leq (m + 1) n }

type Box (k: Type) (o: Ordered k) =
  | MkBox (item: k)

instance Box.instPretty [auto p: Pretty k]: Pretty (Box k o) :=
  { pretty = b => match b with
    | MkBox x => "box of " ++ Pretty.pretty x }

def box [auto ord: Ordered k] (x: k): Box k ord := MkBox x

test "head dictionary" := Pretty.pretty (box 3) == "box of global"
