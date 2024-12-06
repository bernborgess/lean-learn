--
--    author:  bernborgess
--    problem: types - lean-learn
--    created: 09.October.2024 19:54:34
--

import Control.Monad

getList :: (Read a) => IO [a]
getList = map read . words <$> getLine

printList :: (Show a) => [a] -> IO ()
printList = putStrLn . unwords . map show

-- Simple Types
g :: g
g = g

st2 :: b -> g
st2 = st2

st3 :: (g -> a) -> a -> b -> g
st3 f a b = undefined

main = do
  t <- readLn
  replicateM_ t $ do
    n <- getLine
    print ""