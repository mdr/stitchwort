-- expect-error: E-PARTIAL-ESCAPE
-- Recursive calls stored in data that's returned. The same record used
-- inside the definition is fine (`stepper` in accept/partial.sw).
type Handlers : Type =
  | MkHandlers (onStep : Nat -> {Partial} Nat)

handlers : Nat -> {Partial} Handlers
handlers n = MkHandlers (\m -> callStep (handlers m))

callStep : Handlers -> {Partial} Nat
callStep (MkHandlers onStep) = onStep 0
