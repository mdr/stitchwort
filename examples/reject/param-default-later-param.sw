-- expect-error: E-UNKNOWN-NAME
-- A default may use only the parameters before it
-- (docs/proposals/signature-defaults.md §5.2).

def window (width: Nat := height * 2) (height: Nat): Nat := width * height
