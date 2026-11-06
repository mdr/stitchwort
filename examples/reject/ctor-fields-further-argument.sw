-- expect-error: E-PARSE
-- Braces after a constructor in a pattern take no further arguments: a
-- record as its first argument, and more after it, is written `Cons ({ … }) rest`.

type Person = { name: Text, age: Nat }

def firstName: List Person → Text
  | Nil                    => "nobody"
  | Cons { name, .. } rest => name
