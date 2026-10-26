-- expect-error: E-ABILITY
-- A default is computed at each call that leaves it out, so it can't
-- perform operations (docs/proposals/signature-defaults.md §5.2).

def greet (name: Text := IO.readLine()): Text := "Hello, " ++ name
