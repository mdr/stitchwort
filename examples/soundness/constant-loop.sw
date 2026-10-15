-- expect-error: E-TERMINATION
-- A definition with no parameters that refers to itself has nothing that
-- could get smaller. Pairs with every accepted definition that has a
-- parameter to recurse on.
forever : Nat
forever = forever
