type Query = {
  text: Text,
  limit: Nat := 10,
  caseSensitive: Bool := False
}

def everything: Query := { limit = 100 }
