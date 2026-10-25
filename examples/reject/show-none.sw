-- expect-error: E-INSTANCE-NONE
-- `"${e}"` needs a `Show` instance for the type of `e` (docs/proposals/interfaces.md
-- §5.14). A type with a function field gets none derived.

type Handler = { run: Nat → Nat }

def describe (h: Handler): Text := "handler: ${h}"
