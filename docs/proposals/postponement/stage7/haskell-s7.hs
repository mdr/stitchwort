-- SW-988: D2118's case in Haskell (GHC 9.10.3; output in other-runs.txt).
data V = V { dx :: Int, dy :: Int } deriving Show

vs :: [V]
vs = map (\(x, y) -> V x y) [(7, 2), (17, -4)]

-- nothing says the second components' type: defaulting gives Integer
firsts :: [Word]
firsts = map fst [(7, 2), (17, -4)]

main :: IO ()
main = do
  print vs
  print firsts
  print [(7, 2), (17, -4)]
