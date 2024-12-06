expTwo :: Int -> [Int]
expTwo i = replicate (2 ^ i) i

genLogs :: Int -> [Int]
genLogs n = take n $ (0 :) $ concatMap expTwo [0 ..]
