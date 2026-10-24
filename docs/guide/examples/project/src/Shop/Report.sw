-- The program: read orders, one per line, and print a bill.
namespace Shop.Report
import Shop (Order, combine)
import Std (Fail, IO, List, Map)

def main(): {IO, Fail} () :=
  let orders := IO.readAllLines().mapIn Order.read
  let totals := combine orders
  totals.toList.mapIn printTotal
  IO.print "Total: ${bill orders} pence"

def printTotal (item: (Text, Nat)): {IO} () :=
  let (product, quantity) := item
  IO.print "${quantity} x ${product}"

def bill (orders: List Order): Nat := orders.filterMap (.price) |> .sum
