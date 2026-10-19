-- String interpolation: `${e}` inside a text literal inserts `e.toText`.

type Box = { value: Nat }

def world: Text := "world"

test "nat" := "n = ${2 + 3}" == "n = 5"
test "int" := "i = ${-5}" == "i = -5"
test "text" := "hello, ${world}!" == "hello, world!"
test "two" := "${2} + ${3}" == "2 + 3"
test "empty pieces" := "${7}" == "7"
test "braces" := "${ ({ value = 3 } : Box).value }" == "3"
test "nested text" := "${"in" ++ "ner"}" == "inner"
test "dollar escape" := "\${x}" == "$" ++ "{x}"
test "char" := "${'a'}${'}'}" == "a}"
test "bool" := "${1 == 1}, ${True && False}" == "True, False"
