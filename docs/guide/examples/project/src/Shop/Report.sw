-- The program: read orders, one per line, and print a bill.
namespace Shop.Report
import Shop (Order, combine)
import Std (Fail, IO, List, Map)

def main(): {IO, Fail} () :=
  let orders := IO.readAllLines().map Order.read
  let totals := combine orders
  totals.toList.map printTotal
  IO.print "Total: ${bill orders} pence"

def printTotal (item: (Text, Nat)): {IO} () :=
  let (product, quantity) := item
  IO.print "${quantity} x ${product}"

def bill (orders: List Order): Nat := orders.filterMap (.price) |> .sum
