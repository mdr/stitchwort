-- expect-error: E-PARSE
-- A type's parameters in brackets are `auto` ones; an implicit parameter
-- isn't allowed, since a type's other parameters are always given.

type Tagged [a: Type] (x: a) =
  { tag: Nat }
