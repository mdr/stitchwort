-- Named construction: braces right after a constructor name its fields.
type Shape =
  | Dot (ref: Nat) (id: Text)
  | Circle (ref: Nat) (id: Text) (text: Text)

def c: Shape := Circle{ref=1,id="a",text="t"}
def d: Shape :=
  Circle
    { ref = 1
    , id = "a"
    , text = "t"
    }
def e: Shape := Circle {
  ref = 1,
  id = "a",
  text = "t"
}
def f: Option Shape := Some (Dot {ref = 1, id = "x"})
def g: Shape := Circle    { ref = 1, id = "a", text = "t" }
def name (s: Option Shape): Text := match s with
  | Some (Circle{ id, .. }) => id
  | _ => ""
def h: Option (Option Shape) := Some { value = Some { value = Dot {ref = 0, id = "z"} } }
