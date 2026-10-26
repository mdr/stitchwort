-- expect-error: E-TYPE-MISMATCH
-- `Abort.thenEqSome` can't find the first step itself: it must be given,
-- as `(() => binFor locations bins order.item)`.
import Std (Abort, Map, Nat, Option, Text)
import Std.Abort (ensure, toOption)

type Order = { item: Text, quantity: Nat }
type Pick = { item: Text, bin: Nat, left: Nat }

def binFor (locations: Map Text Text) (bins: Map Text Nat) (item: Text): {Abort} Nat :=
  let label := locations.get item |> .orAbort
  bins.get label |> .orAbort

def pickFrom (stock: Map Text Nat) (locations: Map Text Text) (bins: Map Text Nat) (order: Order): Option Pick :=
  toOption (() =>
    let bin := binFor locations bins order.item
    let onHand := stock.get order.item |> .orAbort
    ensure (order.quantity <= onHand)
    { item = order.item, bin, left = onHand - order.quantity })

theorem pickBin (stock: Map Text Nat) (locations: Map Text Text) (bins: Map Text Nat) (order: Order) (pick: Pick)
    (h: pickFrom stock locations bins order = Some pick): toOption (() => binFor locations bins order.item) = Some pick.bin :=
  Abort.thenEqSome _ h (bin found rest => found)
