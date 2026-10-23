-- R19: imports, no blank line between them; a long list follows R7.
namespace Demo
import List (map,   filter )
import Std (Eq)
import Effect (Comp, foldComp, bind,
   Plus, PlusRes)
import Map (
    insert,
    remove
  )

def x: Nat := 1
