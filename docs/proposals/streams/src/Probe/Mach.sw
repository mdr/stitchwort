namespace Probe.Mach

type Machine (a: Type): Type 1 =
  | MkMachine (s: Type) (start: s) (next: s → Pair a s)

def takeFrom [s: Type] (next: s → Pair a s) (state: s) (n: Nat): List a := match n with
  | Zero => []
  | Succ m =>
    let p := next state
    [p.fst, ..takeFrom next p.snd m]

def Machine.take (m: Machine a) (n: Nat): List a := match m with | MkMachine s start next => takeFrom next start n

@[noReceiver]
def Machine.iterate (f: a → a) (x: a): Machine a := MkMachine a x (y => MkPair y (f y))

def Machine.map (m: Machine a) (f: a → b): Machine b := match m with
  | MkMachine s start next => MkMachine s start (st => (let p := next st; MkPair (f p.fst) p.snd))

def Machine.tail (m: Machine a): Machine a := match m with | MkMachine s start next => MkMachine s (next start).snd next

test "take" := ((Machine.iterate (* 2) 1).map (+ 1)).tail.take 4 == [3, 5, 9, 17]

def main(): {IO} () := IO.print "${((Machine.iterate (+ 1) 0).take 20000).sum}"
