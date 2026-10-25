-- expect-error: E-PARTIAL
-- A handler can't make looping code finish (docs/proposals/partial-handlers.md
-- §3.2). A handler around partial code is partial too, so its result can't
-- reach total code: here `finished` would be an endless loop that "returns"
-- a value of a type with no values, and so a proof of anything.
ability Log where
  say: Nat → {Log} ()

type Empty: Type

def forever(): {Log, Partial} Empty :=
  say 1
  forever()

def finished(): Empty :=
  handle forever() with
    | return x => x
    | say n, k => k()

theorem contradiction: Void := emptyVoid (finished())

def emptyVoid: Empty → Void
  | ()
