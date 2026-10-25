-- expect-error: E-ABILITY
-- A handler for `Partial` itself, answering each recursive call, would turn
-- an endless loop into a finished one (docs/proposals/partial.md §8.2).
-- `Partial` has no operations, so no handler can name one
-- (docs/proposals/partial-handlers.md §3.1).
type Empty: Type

def forever(): {Partial} Empty := forever()

def finished(): Empty :=
  handle forever() with
    | return x => x
    | Partial.tick u, k => k()

theorem contradiction: Void := emptyVoid (finished())

def emptyVoid: Empty → Void
  | ()
