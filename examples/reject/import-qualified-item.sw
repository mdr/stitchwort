-- expect-error: E-PARSE
-- A namespace written inside the import's brackets is one token
-- (`List.map`), which isn't an item: importing `map` from `List` writes
-- the namespace in the path. The note gives that form (SW-4274).

import Std (List.map)
