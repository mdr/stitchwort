-- expect-error: E-UNKNOWN-NAME
-- A constructor's named arguments are its fields and its type's parameters,
-- by the names in the type's header: `Option`'s parameter is `a`, not `t`.
-- The error lists what can be named (D3514).

def nothing: Option Text := None [t := Text]
