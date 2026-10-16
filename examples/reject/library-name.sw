-- expect-error: E-UNKNOWN-NAME
-- The library's functions are in namespaces: `split` is `Text.split`, which
-- needs its namespace or an import.
parts : Text -> List Text
parts line = split ',' line
