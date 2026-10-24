-- A field may have a default, written after `:=`. A record literal can then
-- leave it out.
type Greeting = {
  name: Text,
  greeting: Text := "Hello",
  punctuation: Text := "!"
}

def Greeting.render (g: Greeting): Text := "${g.greeting}, ${g.name}${g.punctuation}"

def plain: Greeting := { name = "Ada" }
def excited: Greeting := { name = "Ada", punctuation = "!!!" }

test "defaults fill in" := plain.render == "Hello, Ada!"
test "or are replaced" := excited.render == "Hello, Ada!!!"

-- Leaving a field out is the same as giving its default.
theorem sameValue: plain = { name = "Ada", greeting = "Hello", punctuation = "!" } := rfl

-- A constructor's fields may have defaults too.
type Shape =
  | Circle (id: Text) (radius: Nat)
  | Square (id: Text) (side: Nat := 1)

test "constructor defaults" := Square { id = "unit" } == Square "unit" 1
