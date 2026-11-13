type Key =
  | BirthYear
  | IssueYear

def Key.valid (key: Key) (text: Text): Bool := match key with
  | BirthYear => text.length == 4
  | IssueYear => text.length == 4

def check: Bool := BirthYear.valid "2002"
