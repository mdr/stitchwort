-- Reading orders: a second file of the namespace `Shop`. It sees `Order`
-- without an import, but has its own imports.
namespace Shop
import Std (Fail, List, Text)
import Std.Fail (fail, need)

-- "tea 3" is three teas.
def Order.read (line: Text): {Fail} Order :=
  match line.words with
    | [product, quantity] => { product, quantity = need quantity.toNat "expected a quantity, got '${quantity}'" }
    | _ => fail "expected a product and a quantity, got '${line}'"
