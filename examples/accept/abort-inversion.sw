-- Proofs about `Abort` and `Fail` blocks that succeeded: a warehouse picks
-- an order from the bin that holds its item. Knowing the block gave
-- `Some pick`, `Abort.needEqSome` and `Abort.ensureEqSome` read off what
-- each step gave, one step per lemma.
import Std (Abort, Fail, Map, Nat, Option, Result, Text)
import Std.Abort (ensure, toOption)

type Order = { item: Text, quantity: Nat }
type Bin = { label: Text, aisle: Nat }
type Pick = { item: Text, bin: Bin, quantity: Nat, left: Nat }

type Warehouse = { stock: Map Text Nat, locations: Map Text Text, bins: Map Text Bin }

def pickOrder (warehouse: Warehouse) (order: Order): Option Pick :=
  toOption (() =>
    let onHand := warehouse.stock.get order.item |> .orAbort
    let label := warehouse.locations.get order.item |> .orAbort
    let bin := warehouse.bins.get label |> .orAbort
    ensure (order.quantity <= onHand)
    { item = order.item, bin, quantity = order.quantity, left = onHand - order.quantity })

-- What a pick says about the stock: the item was in stock, as much as was
-- picked and left.
theorem pickStock (warehouse: Warehouse) (order: Order) (pick: Pick) (h: pickOrder warehouse order = Some pick):
    warehouse.stock.get order.item = Some (pick.quantity + pick.left) :=
  Abort.needEqSome h (onHand foundStock rest =>
    Abort.needEqSome rest (label foundLabel rest =>
      Abort.needEqSome rest (bin foundBin rest =>
        Abort.ensureEqSome rest (enough picked =>
          rewrite foundStock, <- Option.someInjective _ _ picked in
            rewrite (omega: order.quantity + (onHand - order.quantity) = onHand) in rfl))))

-- The bin picked from is the one the item's label names.
theorem pickBin (warehouse: Warehouse) (order: Order) (pick: Pick) (h: pickOrder warehouse order = Some pick):
    warehouse.locations.get order.item |> .flatMap warehouse.bins.get = Some pick.bin :=
  Abort.needEqSome h (onHand foundStock rest =>
    Abort.needEqSome rest (label foundLabel rest =>
      Abort.needEqSome rest (bin foundBin rest =>
        Abort.ensureEqSome rest (enough picked =>
          rewrite foundLabel, <- Option.someInjective _ _ picked in foundBin))))

-- The other way: when every step succeeds, the block gives its value.
theorem pickOrderSome (warehouse: Warehouse) (order: Order) (onHand: Nat) (label: Text) (bin: Bin)
    (foundStock: warehouse.stock.get order.item = Some onHand) (foundLabel: warehouse.locations.get order.item = Some label)
    (foundBin: warehouse.bins.get label = Some bin) (enough: order.quantity <= onHand):
    pickOrder warehouse order = Some ({ item = order.item, bin, quantity = order.quantity, left = onHand - order.quantity }) :=
  rewrite foundStock, foundLabel, foundBin, enough in rfl

-- A step that is a call to another `{Abort}` function: `Abort.thenEqSome`
-- is given the call, and says it gave `Some`.
def binFor (warehouse: Warehouse) (item: Text): {Abort} Bin :=
  let label := warehouse.locations.get item |> .orAbort
  warehouse.bins.get label |> .orAbort

def pickFromBin (warehouse: Warehouse) (order: Order): Option (Pair Bin Nat) :=
  toOption (() =>
    let bin := binFor warehouse order.item
    let onHand := warehouse.stock.get order.item |> .orAbort
    ensure (order.quantity <= onHand)
    (bin, onHand - order.quantity))

theorem pickFromBinFound (warehouse: Warehouse) (order: Order) (picked: Pair Bin Nat)
    (h: pickFromBin warehouse order = Some picked): toOption (() => binFor warehouse order.item) = Some picked.fst :=
  Abort.thenEqSome (() => binFor warehouse order.item) h (found foundBin rest =>
    Abort.needEqSome rest (onHand foundStock rest =>
      Abort.ensureEqSome rest (enough result =>
        rewrite foundBin, <- Option.someInjective _ _ result in rfl)))

-- The last step of `binFor` has no rest: `Abort.toOptionNeed` reads it.
theorem binForLabel (warehouse: Warehouse) (item: Text) (bin: Bin) (h: toOption (() => binFor warehouse item) = Some bin):
    warehouse.locations.get item |> .flatMap warehouse.bins.get = Some bin :=
  Abort.needEqSome h (label foundLabel rest =>
    rewrite foundLabel in rewrite Abort.toOptionNeed at rest)

-- With `Fail`, the same: `Fail.needEqOk` and `Fail.ensureEqOk`.
def pickOrFail (warehouse: Warehouse) (order: Order): Result Pick Text :=
  Fail.toResult (() =>
    let onHand := warehouse.stock.get order.item |> .orFail "no stock of ${order.item}"
    let label := warehouse.locations.get order.item |> .orFail "${order.item} has no bin"
    let bin := warehouse.bins.get label |> .orFail "no bin ${label}"
    Fail.ensure (order.quantity <= onHand) "only ${onHand} of ${order.item}"
    { item = order.item, bin, quantity = order.quantity, left = onHand - order.quantity })

theorem pickOrFailEnough (warehouse: Warehouse) (order: Order) (pick: Pick) (h: pickOrFail warehouse order = Ok pick):
    pick.quantity + pick.left = (warehouse.stock.get order.item).getOrElse 0 :=
  Fail.needEqOk h (onHand foundStock rest =>
    Fail.needEqOk rest (label foundLabel rest =>
      Fail.needEqOk rest (bin foundBin rest =>
        Fail.ensureEqOk rest (enough picked =>
          rewrite foundStock, <- Result.okInjective _ _ picked in omega))))

def warehouse: Warehouse := {
  stock = Map.fromList [("bolt", 40), ("nut", 5)],
  locations = Map.fromList [("bolt", "A1"), ("nut", "B2")],
  bins = Map.fromList [("A1", { label = "A1", aisle = 1 })]
}

test "a pick" := pickOrder warehouse { item = "bolt", quantity = 15 } == Some ({ item = "bolt", bin = { label = "A1", aisle = 1 }, quantity = 15, left = 25 })
test "not enough" := pickOrder warehouse { item = "bolt", quantity = 41 } == None
test "no such bin" := pickOrder warehouse { item = "nut", quantity = 1 } == None
test "no such item" := pickOrder warehouse { item = "washer", quantity = 1 } == None
test "the bin" := pickFromBin warehouse { item = "bolt", quantity = 40 } == Some ({ label = "A1", aisle = 1 }, 0)
test "a failure says why" := pickOrFail warehouse { item = "nut", quantity = 1 } == Err "no bin B2"
