-- expect-error: E-UNKNOWN-NAME
-- The library's functions are in namespaces: `lines` is `Text.lines`, which
-- needs its namespace or an import.
def parts (text: Text): List Text := lines text
