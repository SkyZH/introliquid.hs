module Lib
    ( someFunc
    ) where

someFunc :: IO ()
someFunc = putStrLn "someFunc"

{-@ (==>) :: p:Bool -> q:Bool -> {v:Bool | v <=> (p ==> q)} @-} 
False ==> False = True 
False ==> True = True 
True ==> True = True 
True ==> False = False

{-@ (<=>) :: p:Bool -> q:Bool -> {v:Bool | v <=> (p <=> q)} @-} 
False <=> False = True 
False <=> True = False 
True <=> True = True 
True <=> False = False

{-@ type TRUE  = {v:Bool | v     } @-}
{-@ type FALSE = {v:Bool | not v } @-}

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

