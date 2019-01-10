{-@ LIQUID "--short-names" @-}
{-@ LIQUID "--higherorder" @-}

module Ex2 where

{-@ size  :: xs:[a] -> {v:Int | v = size xs} @-}
{-@ invariant {v:[a] | size v >= 0} @-}

infixr 9 ==>

{-@ (==>) :: p:Bool -> q:Bool -> {v:Bool | v <=> (p ==> q)} @-}
False ==> False = True
False ==> True  = True
True  ==> True  = True
True  ==> False = False

{-@ (<=>) :: p:Bool -> q:Bool -> {v:Bool | v <=> (p <=> q)} @-}
False <=> False = True
False <=> True  = False
True  <=> True  = True
True  <=> False = False

{-@ type TRUE  = {v:Bool | v    } @-}
{-@ type FALSE = {v:Bool | not v} @-}

{-@ ex0 :: TRUE @-}
ex0 = True

{-@ ex0' :: FALSE @-}
ex0' = False

{-@ ex1 :: Bool -> TRUE @-}
ex1 b = b || not b

{-@ ex2 :: Bool -> FALSE @-}
ex2 b = b && not b

{-@ ex3 :: Bool -> Bool -> TRUE @-}
ex3 a b = (a && b) ==> a

{-@ ex4 :: Bool -> Bool -> TRUE @-}
ex4 a b = (a && b) ==> b

-- Exercise 2.1
{-@ ex3' :: Bool -> Bool -> TRUE @-}
ex3' a b = a ==> a || b

{-@ ex6 :: Bool -> Bool -> TRUE @-}
ex6 a b = (a && (a ==> b)) ==> b

{-@ ex7 :: Bool -> Bool -> TRUE @-}
ex7 :: Bool -> Bool -> Bool
ex7 a b = a ==> (a ==> b) ==> b

{-@ exDeMorgan1 :: Bool -> Bool -> TRUE @-}
exDeMorgan1 a b = not (a || b) <=> (not a && not b)

-- Exercise 2.2
{-@ exDeMorgan2 :: Bool -> Bool -> TRUE @-}
exDeMorgan2 a b = not (a && b) <=> (not a || not b)

{-@ ax0 :: TRUE @-}
ax0 = 1 + 1 == 2

{-@ ax1 :: Int -> TRUE @-}
ax1 :: Int -> Bool
ax1 x = x < x + 1

{-@ ax2 :: Int -> TRUE @-}
ax2 :: Int -> Bool
ax2 x = (x < 0) ==> (0 <= 0 - x)

{-@ ax3 :: Int -> Int -> TRUE @-}
ax3 :: Int -> Int -> Bool
ax3 x y = (0 <= x) ==> (0 <= y) ==> (0 <= x + y)

{-@ ax4 :: Int -> Int -> TRUE @-}
ax4 :: Int -> Int -> Bool
ax4 x y = (x == y - 1) ==> (x + 2 == y + 1)

{-@ ax5 :: Int -> Int -> Int -> TRUE @-}
ax5 :: Int -> Int -> Int -> Bool
ax5 x y z = (x <= 0 && x >= 0) ==> (y == x + z) ==> (y == z)

-- exercise 2.3
{-@ ax6 :: Int -> Int -> TRUE @-}
ax6 :: Int -> Int -> Bool
ax6 x y = (y >= 0) ==> (x <= x + y)

{-@ measure f :: Int -> Int @-}

{-@ congruence :: (Int -> Int) -> Int -> Int -> TRUE @-}
congruence :: (Int -> Int) -> Int -> Int -> Bool
congruence f x y = (x == y) ==> (f x == f y)

{-@ fx1 :: (Int -> Int) -> Int -> TRUE @-}
fx1 :: (Int -> Int) -> Int -> Bool
fx1 f x =     (x == f (f (f x)))
          ==> (x == f (f (f (f x))))
          ==> (x == f x)

{-@ measure size @-}
size       :: [a] -> Int
size []    = 0
size (x:xs) = 1 + size xs

{-@ fx0 :: [a] -> [a] -> TRUE @-}
fx0 xs ys = (xs == ys) ==> (size xs == size ys)

{-@ fx2 :: a -> [a] -> TRUE @-}
fx2 :: a -> [a] -> Bool
fx2 x xs = (0 < size ys) 
    where ys = x : xs

    