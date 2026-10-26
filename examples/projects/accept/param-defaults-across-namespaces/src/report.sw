-- Calls them from another namespace, leaving defaults out and naming them.
namespace Report
import Layout (padding, label, columns)
import Std (Nat, Text)

def heading: Text := label "Total"

def wide: Nat := padding "ab" (width := 5)

theorem threeColumns: columns 3 = 5 := rfl

test "defaults across namespaces" :=
  heading == "Total:" && padding "ab" == 2 && wide == 3 && columns 3 (gap := 2) == 7
