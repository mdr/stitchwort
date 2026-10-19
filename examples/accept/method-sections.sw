-- Method sections. `.f args` is `\x => x.f args`, dot notation with the
-- receiver left out (docs/syntax.md, "Method sections"). Chains work
-- (`.name.length`), the head section takes the arguments after it, and as an
-- argument a section takes none unless it's in brackets (`.map (.greet "Hi")`).
-- `xs |> .drop 1` is exactly `xs.drop 1`. A section is checked like a lambda,
-- so it needs the receiver's type from where it's used: a known function type,
-- a pipe's left side, or an annotation.

type Person = { name: Text, age: Nat }

def Person.greet (greeting: Text) (p: Person): Text := greeting ++ ", " ++ p.name

def people: List Person := [{ name = "Ann", age = 30 }, { name = "Bo", age = 4 }]

-- A section where a function type is known.
def names: List Text := people.map .name

test "map a field" := names == ["Ann", "Bo"]

-- A chain.
def lengths: List Nat := people.map .name.length

test "a chain" := lengths == [3, 2]

-- A method with an argument needs brackets; the receiver is `greet`'s last
-- parameter, wherever it sits.
def greetings: List Text := people.map (.greet "Hi")

test "a section with an argument" := greetings == ["Hi, Ann", "Hi, Bo"]

-- Postponed: `List.map`'s list comes after the section, so the section is
-- checked once `people` has fixed its type.
def names2: List Text := List.map .name people

test "a section before the collection" := names2 == names

-- Pipelines.
def piped: Nat := [1, 2, 3, 4] |> .drop 1 |> .map (\x => x * 2) |> .sum

def ages: Nat := people |> .map .age |> .sum

test "pipeline" := piped == 18
test "pipeline over a field" := ages == 34

-- A multi-line pipeline: the `|>` starts each line.
def multi: Nat :=
  people
    |> .map .age
    |> .filter (\a => a == 4)
    |> .length

test "multi-line" := multi == 1

-- The receiver isn't the first parameter: `Text.split` takes the separator
-- first, the text last.
def fields (line: Text): List Text := line |> .split ','

test "split" := fields "a,b,c" == ["a", "b", "c"]
test "split each line" := ["a,b", "c"].map (.split ',') == [["a", "b"], ["c"]]

-- An annotation gives the receiver when nothing else does.
def dropFirst: List Nat -> List Nat := .drop 1

test "annotated" := dropFirst [1, 2, 3] == [2, 3]
test "annotated inline" := (.drop 1: List Nat -> List Nat) [1, 2, 3] == [2, 3]

-- A function parameter's type is known, so the section can be passed to it.
def apply (f: Text -> Nat) (t: Text): Nat := f t

test "a function parameter" := apply .length "abc" == 3
