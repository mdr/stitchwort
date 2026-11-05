namespace Proofs

import Types (Path)

def Path.extend (path: Path) (more: List Nat): Path := { caves = path.caves ++ more }

def Completes (sofar: Path) (rest: List Nat): Path := sofar.extend rest

test "extend" := (Completes ({ caves = [1] }) [2]).caves == [1, 2]
