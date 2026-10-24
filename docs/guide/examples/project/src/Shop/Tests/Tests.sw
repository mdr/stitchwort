-- The shop's tests, in a namespace of their own so that running the program
-- doesn't check them.
namespace Shop.Tests
import Shop (..)
import Shop.Report (bill)
import Std (Fail, Map)

def read (line: Text): Result Order Text := Fail.toResult (() => Order.read line)

test "reads an order" := read "tea 3" == Ok ({ product = "tea", quantity = 3 })
test "refuses a bad quantity" := read "tea lots" == Err "expected a quantity, got 'lots'"
test "prices an order" := ({ product = "milk", quantity = 2 }: Order).price == Some 180
test "an unknown product has no price" := ({ product = "cake", quantity = 1 }: Order).price == None
test "combines orders" := (combine [{ product = "tea", quantity = 1 }, { product = "tea", quantity = 2 }]).get "tea" == Some 3
test "bills only what it sells" := bill [{ product = "tea", quantity = 2 }, { product = "cake", quantity = 9 }] == 500
