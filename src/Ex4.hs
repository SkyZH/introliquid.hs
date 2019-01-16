{-@ LIQUID "--short-names"         @-}
{-@ LIQUID "--no-termination"      @-}
{-@ LIQUID "--scrape-used-imports" @-}

module Ex4 (
    head',
    head'',
    safeLookup,
    unsafeLookup,
    vectorSum,
    absoluteSum,
    vectorSum',
    absoluteSum'
) where

import Prelude      hiding (head, abs, length)
import Data.List    (foldl')
import Data.Vector  hiding (head, foldl')


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

-- exercise 4.4
vectorSum :: Vector Int -> Int
vectorSum vec = go 0 0
    where
        go acc i
            | i < sz = go (acc + (vec ! i)) (i + 1)
            | otherwise = acc
        sz = length vec

abz :: Int -> Int
abz a = if a < 0 then (-a) else a

-- exercise 4.5
{-@ absoluteSum :: Vector Int -> Nat @-}
absoluteSum :: Vector Int -> Int
absoluteSum vec = absoluteSum' 0 0
    where 
        absoluteSum' acc i
            | i < sz = absoluteSum'' acc i
            | otherwise = acc
            where
                absoluteSum'' acc i = absoluteSum' (acc + abz (vec ! i)) (i + 1)
        sz = length vec

loop :: Int -> Int -> a -> (Int -> a -> a) -> a
loop lo hi base f =  go base lo
    where
        go acc i
            | i < hi    = go (f i acc) (i + 1)
            | otherwise = acc

vectorSum'      :: Vector Int -> Int
vectorSum' vec  = loop 0 n 0 body 
    where
        body i acc  = acc + (vec ! i)
        n           = length vec

-- exercise 4.7
{-@ absoluteSum' :: Vector Int -> Int @-}
absoluteSum' :: Vector Int -> Int
absoluteSum' vec = loop 0 n 0 body
  where
    body i acc   = acc + abz (vec ! i)
    n            = length vec

-- exercise 4.8
{-@ dotProduct :: x:Vector Int -> {y:Vector Int | vlen y == vlen x} -> Int @-}
dotProduct :: Vector Int -> Vector Int -> Int
dotProduct x y = loop 0 sz 0 body
    where
        sz = length x
        body i acc= acc + (x ! i) * (y ! i)
