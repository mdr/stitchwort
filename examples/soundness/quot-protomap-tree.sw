-- expect-error: E-NOT-A-CONSTRUCTOR
-- R2 on the step 1.6 prototype (docs/proposals/map-equality.md §7.6, §14.2
-- property 5): a `ProtoMap`'s representative, and so its tree, can't be
-- reached by matching on the quotient. Two maps with the same entries can
-- have different trees (accept/quot-protomap.sw's `forwardsRoot` and
-- `backwardsRoot`), so a root key read this way would tell equal maps apart.
-- Pairs with accept/quot-protomap.sw, whose operations use `Quot.lift`.
import Std (Map, Quot)
import Std.Map.Tree (Tip, Bin)

type ProtoMap (k: Type) (v: Type) [auto ord: Ord k] = { raw: Quot (Map k v [ord := ord]) Map.Equiv }

def rootKey (m: ProtoMap Nat Text): Option Nat :=
  match m.raw with
    | Quot.mk r => match r.tree with
      | Tip => None
      | Bin _ _ key _ _ => Some key
