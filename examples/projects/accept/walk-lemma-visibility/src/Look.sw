namespace Look

import Std (Parse, Option, Nat)

def look(): {Parse Nat} Option Nat := Parse.next (n => True)
