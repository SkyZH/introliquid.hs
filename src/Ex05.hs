module Ex05 where

{-@ type NonZero = {v:Int | v /= 0} @-}
{-@ type Zero    = {v:Int | v == 0} @-}

{-@ die :: {v:String | false} -> a @-}
die = error

{-@ divide :: Int -> NonZero -> Int @-}
divide :: Int -> Int -> Int
divide _ 0 = die "divide-by-zero"
divide x n = x `div` n

avg2 x y = divide (x + y) 2
avg3 x y z = divide (x + y + z) 3

size :: [a] -> Int
size [] = 0
size (_:xs) = 1 + size xs

notEmpty :: [a] -> Bool
notEmpty [] = False
notEmpty (_:_) = True

{-@ measure notEmpty @-}
{-@ type NEList a = {v:[a] | notEmpty v} @-}
{-@ size :: xs:[a] -> {v:Nat | notEmpty xs => v > 0} @-}


{-@ average :: NEList Int -> Int @-}
average xs = divide total elems
  where
    total = sum xs
    elems = size xs

-- exercise 5.1
average' :: [Int] -> Maybe Int
average' xs
  | ok = Just $ divide (sum xs) elems
  | otherwise = Nothing
  where
    elems = size xs
    ok = elems /= 0

{-@ type Pos = {v:Int | 0 < v} @-}

-- exercise 5.2
{-@ size1 :: xs:NEList a -> Pos @-}
size1 :: [a] -> Int
size1 (_:_) = 1
size1 (_:xs) = 1 + size1 xs

{-@ size2 :: xs:[a] -> {v:Nat | notEmpty xs => v > 0} @-}
size2 :: [a] -> Int
size2 [] = 0
size2 (_:xs) = 1 + size2 xs

{-@ lhead :: NEList a -> a @-}
lhead (x:_) = x
lhead [] = die "Fear not!"

{-@ ltail :: NEList a -> [a] @-}
ltail (_:xs) = xs
ltail [] = die "Dead!"

-- exercise 5.3
safeHead :: [a] -> Maybe a
safeHead xs
  | lnull xs = Nothing
  | otherwise = Just $ lhead xs

{-@ lnull :: xs:[a] -> {v:Bool | notEmpty xs <=> v == False} @-}
lnull :: [a] -> Bool
lnull [] = True
lnull (_:_) = False

{-@ groupEq :: (Eq a) => [a] -> [NEList a] @-}
groupEq [] = []
groupEq (x:xs) = (x:ys) : groupEq zs
  where
    (ys, zs) = span (x ==) xs

{-@ foldr2 :: (a -> a -> a) -> NEList a -> a @-}
foldr2 f (x:xs) = foldr f x xs
foldr2 _ [] = die "foldr1"

{-@ sum1 :: (Num a) => NEList a -> a @-}
sum1 [] = die "cannot add up empty list"
sum1 xs = foldr1 (+) xs

sumOK = sum1 [1, 2, 3, 4, 5]

-- exercise 5.4
{-@ wtAverage :: NEList (Pos, Pos) -> Int @-}
wtAverage wxs = divide totElems totWeight
                  where
                    elems = map1 (\(w, x) -> w * x) wxs
                    weights = map1 (\(w, _) -> w) wxs
                    totElems = sum elems
                    totWeight = sum weights
                    sum = foldr2 (+)

{-@ map1 :: (a -> b) -> NEList a -> NEList b @-}
map1 :: (a -> b) -> [a] -> [b]
map1 _ [] = []
map1 f (x:xs) = f x : map f xs

-- exercise 5.5
{-@ risers :: (Ord a) => NEList a -> NEList [a] @-}
risers :: (Ord a) => [a] -> [[a]]
risers [] = []
risers [x] = [[x]]
risers (x:y:etc)
  | x <= y = (x:s) : ss
  | otherwise = [x] : (s:ss)
    where
      (s, ss) = safeSplit $ risers (y:etc)

{-@ safeSplit :: NEList a -> (a, [a]) @-}
safeSplit (x:xs) = (x, xs)
safeSplit _ = die "don't worry, be happy"
