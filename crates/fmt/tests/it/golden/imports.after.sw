-- R19: imports, no blank line between them; a long list follows R7; `as`
-- in an item is spaced like any word.
namespace Demo
import List (map, filter)
import Std (Eq)
import Text (split as cut, join as glue)
import Map (Map as Table, insert as put)
import Effect (Comp, foldComp, bind, Plus, PlusRes)
import Map (insert, remove)

def x: Nat := 1
