-- expect-error: E-POSITIVITY
-- R10 on the step 1.6 prototype (docs/proposals/map-equality.md §11.2,
-- §14.2 property 8): a tree whose children are in a `ProtoMap`, the shape
-- `Map` will have in stage 2, is refused with the message for a type used
-- inside a quotient. Pairs with accept/mutual-data.sw (a tree and a forest
-- defined together).
import Std (Map, Quot)

type ProtoMap (k: Type) (v: Type) [auto ord: Ord k] = { raw: Quot (Map k v [ord := ord]) Map.Equiv }

type Tree = { name: Text, children: ProtoMap Text Tree }
