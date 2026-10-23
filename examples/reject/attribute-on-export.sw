-- expect-error: E-ATTRIBUTE
-- Renaming an export is a later stage (docs/proposals/attributes.md §9.1).
@[js.name "renderDrawing"]
export def render (n: Nat): Nat := n
