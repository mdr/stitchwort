-- The shop's model: products, prices and orders.
namespace Shop
import Std (List, Map, Nat, Text)

type Product = { name: Text, pence: Nat }

type Order = { product: Text, quantity: Nat }

def catalogue: Map Text Product := Map.fromList [
  ("tea", { name = "tea", pence = 250 }),
  ("milk", { name = "milk", pence = 90 }),
  ("biscuits", { name = "biscuits", pence = 120 })
]

-- The price of an order, or `None` for a product the shop doesn't sell.
def Order.price (order: Order): Option Nat := catalogue.get order.product |> .map (product => product.pence * order.quantity)

-- Orders of the same product, added up, in the product's name order.
def combine (orders: List Order): Map Text Nat :=
  orders.foldLeft Map.empty (totals order => totals.insertWith order.product order.quantity (a b => a + b))
