-- expect-error: E-PARTIAL-ESCAPE
-- Recursive calls stored in data that's returned. The same record used
-- inside the definition is fine (`stepper` in accept/partial.sw).
type Handlers: Type =
  | MkHandlers (onStep: Nat -> {Partial} Nat)

def handlers (n: Nat): {Partial} Handlers := MkHandlers (m => callStep (handlers m))

def callStep: Handlers -> {Partial} Nat
  | MkHandlers onStep => onStep 0
