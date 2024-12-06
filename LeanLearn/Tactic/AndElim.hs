import Control.Monad
import GHC.Natural
import GHC.Num (integerToNatural)

-- Motivation: Extract the programmatic part out of AndElim
-- apart from metaprogramming and parsing.

newtype Term = Term {type' :: String} deriving (Show)

type Conjunction = [Term]

maybeTail :: [a] -> Maybe [a]
maybeTail [] = Nothing
maybeTail (x : xs) = Just xs

maybeHead :: [a] -> Maybe a
maybeHead [] = Nothing
maybeHead (x : xs) = Just x

getProof :: Natural -> Conjunction -> Maybe Conjunction
getProof 0 hyp = pure hyp
getProof i hyp = do
    im <- minusNaturalMaybe i 1
    rc <- getProof im hyp
    maybeTail rc

-- #########################################################################

jn x r k =
    case k of
        0 -> Just x
        _ -> r (k - 1)

(!?) :: [a] -> Int -> Maybe a
{-# INLINEABLE (!?) #-}
xs !? n
    | n < 0 = Nothing
    | otherwise = foldr jn (const Nothing) xs n

getLengthAnd :: Conjunction -> Natural
getLengthAnd = toEnum . length

andElim :: Conjunction -> Natural -> Maybe Term
andElim val i = do
    let len = getLengthAnd val
    guard (i < len)
    guard (i >= 0)
    val !? fromEnum i

h1 = [Term "A", Term "B", Term "C"]

-- Meta code under Tactic monad
evalAndElim :: a -> Maybe Term
evalAndElim stx = do
    (val, i) <- undefined stx
    andElim val i

type Name = String

data Expr
    = App Expr Expr Expr
    | Lam Name Expr Expr Expr

-- Test heading and tailing for the index
safeExprIndex :: Expr -> Natural -> Expr
safeExprIndex = undefined