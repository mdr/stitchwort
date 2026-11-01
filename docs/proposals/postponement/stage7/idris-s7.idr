-- SW-988: D2118's case in Idris 2 (run with Idris 2 0.8.0; output in
-- other-runs.txt).
module Main

record V where
  constructor MkV
  dx : Integer
  dy : Integer

Show V where
  show v = "(" ++ show v.dx ++ ", " ++ show v.dy ++ ")"

vs : List V
vs = map (\(dx, dy) => MkV dx dy) [(7, 2), (17, -4)]

-- nothing says the second components' type: the default hint gives Integer
firsts : List Nat
firsts = map fst [(7, 2), (17, -4)]

main : IO ()
main = do
  printLn vs
  printLn firsts
  printLn [(7, 2), (17, -4)]
