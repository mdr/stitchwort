-- `needsToken` is proved with A's procedure.
namespace Day

import Base (needsToken)
import A (decA)

def client: Nat := needsToken

test "client" := client == 1
