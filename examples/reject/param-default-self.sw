-- expect-error: E-MUTUAL-SIGNATURE
-- A default is checked from the header, before the body, so it can't use
-- the definition itself (docs/proposals/signature-defaults.md §5.2).

def depth (n: Nat := depth 0): Nat := n
