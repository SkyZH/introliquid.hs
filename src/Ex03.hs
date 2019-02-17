{-@ LIQUID "--short-names" @-}
{-@ LIQUID "--higherorder" @-}
{-@ LIQUID "--no-termination" @-}

module Ex03 where

{-@ type Zero = {v:Int | v == 0} @-}
{-@ type NonZero = {v:Int | v /= 0} @-}
{-@ type TRUE  = {v:Bool | v    } @-}
{-@ type FALSE = {v:Bool | not v} @-}

{-@ zero :: Zero @-}
zero = 0 :: Int

{-@ one, two, three :: NonZero @-}
one = 1 :: Int
two = 2 :: Int
three = 3 :: Int

{-@ type Nat = {v:Int | 0 <= v} @-}
{-@ type Even = {v:Int | v mod 2 == 0} @-}
{-@ type Lt233 = {v:Int | v < 233} @-}

{-@ zero' :: Nat @-}
zero' = zero

{-@ zero'' :: Even @-}
zero'' = zero

{-@ zero''' :: Lt233 @-}
zero''' = zero

{-@ die :: {v:String | false} -> a @-}
die = error

cannotDie = if 1 + 1 == 3
    then die "horrible death"
    else ()


{-@ divide :: Int -> NonZero -> Int @-}
divide :: Int -> Int -> Int
divide n 0 = die "division by zero"
divide n d = n `div` d

-- exercise 3.1
{-@ avg :: [Int] -> Int @-}

avg :: [Int] -> Int
avg xs = if n == 0
    then 0
    else divide total n
    where 
        total = sum xs
        n = length xs

{-@ abs' :: Int -> Nat @-}
abs' :: Int -> Int
abs' n
    | 0 < n = n
    | otherwise = 0 - n

calc = do
    putStrLn "Enter number"
    n <- readLn
    putStrLn "Enter denominator"
    d <- readLn
    putStrLn $ result n d
    calc

result n d
    | isPositive d = "Result = " ++ show (n `divide` d)
    | otherwise = "Please enter positive number"


-- exercise 3.2
{-@ isPositive :: x:a -> {v:Bool | v <=> x > 0} @-}
isPositive x = x > 0

-- exercise 3.3
{-@ lAssert :: TRUE -> a -> a @-}
lAssert True x = x
lAssert False _ = die "assertion fails!"

yes = lAssert (1 + 1 == 2) ()

truncate :: Int -> Int -> Int
truncate i max
    | i' <= max' = i
    | otherwise = max' * (i `divide` i')
    where
        i' = abs' i
        max' = abs' max

