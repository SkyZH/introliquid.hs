module Ex4 where

import Prelude hiding (length)
import Data.Vector

{-@ type VectorN a N = {v: Vector a | vlen v == N } @-}

{-@ type Btwn Lo Hi = {v:Int | Lo <= v && v < Hi} @-}

{-@ twoLangs :: VectorN String 2 @-}
twoLangs = fromList ["haskell", "javascript"]

eeks = [ok, yup, nono]
    where
        ok = twoLangs ! 0
        yup = twoLangs ! 1
        nono = twoLangs ! 1

{-@ type NEVector a = {v:Vector a | 0 < vlen v} @-}
{-@ head' :: NEVector a -> a @-}
head' :: Vector a -> a
head' vec = vec ! 0

-- exercise 4.1
head'' :: Vector a -> Maybe a
head'' vec = if length vec > 0 then
        Just $ vec ! 0
    else
        Nothing

-- exercise 4.2
{-@ unsafeLookup :: idx:Nat -> {v:Vector a | idx < vlen v} -> a @-}
unsafeLookup index vec = vec ! index

-- exercise 4.3
{-@ safeLookup :: Vector a -> Int -> Maybe a @-}
safeLookup x i
    | ok = Just (x ! i)
    | otherwise = Nothing
    where
        ok = 0 <= i && i < length x