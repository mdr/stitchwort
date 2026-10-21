-- `Show` and interpolation (docs/proposals/interfaces.md §5.14, §6.4):
-- `"${e}"` is `Show.toText e`. `toText` is for people, `toSource` is what
-- elements of lists, tuples, records and constructors use: text is quoted
-- only inside containers.

type Dir = | L | R

type Shape = | Circle (radius: Nat) | Rect (w: Nat) (h: Nat) | Dot

type Tree (a: Type) = | Leaf | Node (l: Tree a) (x: a) (r: Tree a)

-- A record; the proof field is left out of the text.
type Item = { name: Text, price: Nat, positive: price = price }

type Pair2 (a: Type) (b: Type) = { first: a, second: b }

-- A module's own instance replaces the derived one.
type Point = { x: Nat, y: Nat }

def Point.toText (p: Point): Text := "(${p.x}, ${p.y})"

instance Point.instShow: Show Point := Show.fromText Point.toText

def item: Item := { name = "tea", price = 3, positive = rfl }

-- `toText` and `toSource` differ only for `Text` and `Char`.
test "text" := "${"tea"}" == "tea"
test "text source" := Show.toSource "tea" == "\"tea\""
test "char" := "${'a'}" == "a"
test "char source" := Show.toSource 'a' == "'a'"
test "numbers" := "${2 + 3} ${-5}" == "5 -5"
test "bool and ordering" := "${True} ${Less}" == "True Less"

-- Elements are shown with `toSource`.
test "list of texts" := "${["a", "b"]}" == "[\"a\", \"b\"]"
test "list of chars" := "${['a', 'b']}" == "['a', 'b']"
test "empty list" := "${([]: List Nat)}" == "[]"
test "nested lists" := "${[[1, 2], [3]]}" == "[[1, 2], [3]]"
test "pair" := "${("x", 1)}" == "(\"x\", 1)"
test "triple" := "${(1, 'c', "s")}" == "(1, ('c', \"s\"))"
test "maybe" := "${Just "a"} ${(Nothing: Maybe Nat)}" == "Just \"a\" Nothing"
test "maybe nested" := "${Just (Just 1)}" == "Just (Just 1)"
test "maybe negative" := "${Just (-5)}" == "Just (-5)"
test "maybe list" := "${Just [1, 2]}" == "Just [1, 2]"

-- Escapes, as in a literal.
test "escapes" := "${["a\"b\n\\"]}" == "[\"a\\\"b\\n\\\\\"]"
test "dollar" := Show.toSource ("\$" ++ "{x}") == "\"\\\$" ++ "{x}\""
test "quote char" := Show.toSource '\'' == "'\\''"

-- Derived.
test "enum" := "${L} ${R}" == "L R"
test "fields" := "${Circle 2} ${Rect 3 4} ${Dot}" == "Circle 2 Rect 3 4 Dot"
test "shapes" := "${[Circle 2, Dot]}" == "[Circle 2, Dot]"
test "recursive" := "${Node Leaf 1 (Node Leaf 2 Leaf)}" == "Node Leaf 1 (Node Leaf 2 Leaf)"
test "parameter" := "${Node Leaf "a" Leaf}" == "Node Leaf \"a\" Leaf"
test "record" := "${item}" == "{ name = \"tea\", price = 3 }"
test "record in a list" := "${[item]}" == "[{ name = \"tea\", price = 3 }]"
test "generic record" := "${({ first = "a", second = 1 }: Pair2 Text Nat)}" == "{ first = \"a\", second = 1 }"
test "record in a constructor" := "${Just item}" == "Just { name = \"tea\", price = 3 }"

-- The module's own instance.
test "own instance" := "${({ x = 1, y = 2 }: Point)}" == "(1, 2)"
test "own instance inside" := "${[({ x = 1, y = 2 }: Point)]}" == "[(1, 2)]"

-- A dictionary is found through any generic function.
def shout [auto s: Show a] (x: a): Text := "${x}!"

test "generic" := shout 7 == "7!" && shout "hi" == "hi!"

-- Vectors and `Fin`.
test "vec" := "${VCons 1 (VCons 2 VNil)}" == "[1, 2]"
test "fin" := "${(Fin.ofNat 2: Fin 5)}" == "2"

-- Pieces and nesting.
test "pieces" := "a${1}b${"c"}d" == "a1bcd"
test "nested interpolation" := "${"x${1}"}" == "x1"
