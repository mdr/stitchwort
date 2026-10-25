-- expect-error: E-PARSE
-- Braces after a constructor name its fields and take no further
-- arguments: a record as its first argument is written `Cons ({ … }) rest`.

type Person = { name: Text, age: Nat }

def firstName: List Person → Text
  | Nil                    => "nobody"
  | Cons { name, .. } rest => name
