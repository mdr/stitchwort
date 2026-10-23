-- `x.f y` calls `T.f` with `x` in the place of its `T` parameter, so a
-- function defined for a type reads like a method.
type Person = { name: Text, age: Nat }

def Person.greet (greeting: Text) (p: Person): Text := greeting ++ ", " ++ p.name

def people: List Person := [{ name = "Ann", age = 30 }, { name = "Bo", age = 4 }]

-- `.name` on its own is a section: the function `p => p.name`.
def names: List Text := people.map .name

-- `|>` feeds the left side in as the last argument, so pipelines read
-- top to bottom.
def totalAge: Nat :=
  people
    |> .map .age
    |> .sum

def greetings: List Text := people.map (.greet "Hi")

test "names" := names == ["Ann", "Bo"]
test "total" := totalAge == 34
test "method call" := (Person.greet "Hi" { name = "Cy", age = 1 }) == "Hi, Cy"
test "greetings" := greetings == ["Hi, Ann", "Hi, Bo"]
