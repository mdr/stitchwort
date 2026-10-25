-- expect-error: E-ATTRIBUTE
@[js.tag "type"]
interface Sized (a: Type) = { size: a → Nat }
