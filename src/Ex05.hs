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

