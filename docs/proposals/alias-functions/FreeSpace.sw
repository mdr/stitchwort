-- An alias whose value flows through `List.scanLeft`.
import Std (List)

def FreeSpace: Type := List Nat

def FreeSpace.of (spans: List Nat): FreeSpace := spans

def FreeSpace.move (free: FreeSpace) (file: Nat): FreeSpace := Cons file free

-- The initial state comes before the step function.
def steps (files: List Nat): List FreeSpace := List.scanLeft files (FreeSpace.of [1]) (free file => free.move file)

-- Through a `let` with no annotation.
def viaLet (files: List Nat): List FreeSpace :=
  let initial := FreeSpace.of [1]
  List.scanLeft files initial (free file => free.move file)

-- A function whose first argument fixes the state type before the initial
-- state is seen, as `List.mapZipWithScanLeft` does in the day 9 proofs.
def zipScan (g: a → b → c) (xs: List a) (z: b) (f: b → a → b): List c := List.zipWith xs (List.scanLeft xs z f) g

def stateFixedFirst (files: List Nat): List Nat :=
  zipScan (file free => List.length (FreeSpace.move free file)) files (FreeSpace.of [1]) (free file => free.move file)
