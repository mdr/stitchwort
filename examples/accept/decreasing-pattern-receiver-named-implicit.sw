-- A pattern's `[n := m]` names an implicit field; it isn't one of the
-- positional arguments, so `coin` is the constructor's first explicit field
-- (a `Coin`) and `coin.value` means `Coin.value`.
type Coin = { cents: Nat }
type Pile: Nat → Type = | Empty: Pile 0 | Put [n: Nat] (coin: Coin) (rest: Pile n): Pile (Succ n)

def Pile.value: Pile n → Nat
  | Empty => 0
  | Put [n := m] coin _ => coin.value

def Coin.value (coin: Coin): Nat := coin.cents
