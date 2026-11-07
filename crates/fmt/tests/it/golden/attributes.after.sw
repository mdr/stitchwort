-- R15: attributes stay where they are; spacing inside follows R4 to R6.
@[js.name "q"]
def q: Nat := 1

@[
  js.tag "kind",
  js.other "x"
]
type Message =
  | Note (@[js.name "note_id"] id: Nat) (body: Text)
  | Other (body: Text)

type Pet = { @[js.name "n"] name: Text, age: Nat }
