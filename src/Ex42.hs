{-@ LIQUID "--short-names"         @-}
{-@ LIQUID "--no-termination"      @-}
{-@ LIQUID "--scrape-used-imports" @-}
module Ex42 (
    Sparse(..),
    dotProd,
    dotProd',
    fromList,
    test1,
    plus,
    test2,
    insert,
    insertSort
) where

import Prelude      hiding (head, abs, length)
import Data.List    (foldl')
import Data.Vector  hiding (head, foldl', fromList, all, (++))
import Data.Maybe

{-@ type Btwn Lo Hi = {v:Int | Lo <= v && v < Hi} @-}

{-@ data Sparse a = SP { spDim :: Nat
                       , spElems :: [(Btwn 0 spDim, a)]} @-}
data Sparse a = SP { spDim :: Int
                   , spElems :: [(Int, a)]}

okSP :: Sparse String
okSP = SP 5 [ (0, "cat")
            , (3, "dog")]

{-@ type SparseN a N = {v:Sparse a | spDim v == N} @-}

{-@ dotProd :: x:Vector Int -> SparseN Int (vlen x) -> Int @-}
dotProd :: Vector Int -> Sparse Int -> Int
dotProd x (SP _ y) = go 0 y
    where
    go sum ((i, v) : y') = go (sum + (x ! i) * v) y'
    go sum []            = sum

{-@ dotProd' :: x:Vector Int -> SparseN Int (vlen x) -> Int @-}
dotProd' :: Vector Int -> Sparse Int -> Int
dotProd' x (SP _ y) = foldl' body 0 y
    where
    body sum (i, v) = sum + (x ! i) * v

-- exercise 4.9
{-@ fromList :: dim:Nat -> [(Btwn 0 dim, a)] -> Maybe (SparseN a dim) @-}
fromList :: Int -> [(Int, a)] -> Maybe (Sparse a)
fromList dim elts = if valid then Just (SP dim elts) else Nothing
    where
        valid = all body elts
        body (idx, _) = idx < dim

{-@ test1 :: SparseN String 3 @-}
test1 = fromJust $ fromList 3 [(0, "cat"), (2, "mouse")]


-- exercise 4.10

{-@ die :: {v:String | false} -> a @-}
die = error

{-@ plus :: v:Sparse a -> SparseN a (spDim v) -> SparseN a (spDim v) @-}
plus :: (Num a) => Sparse a -> Sparse a -> Sparse a
plus (SP dimx x) (SP dimy y)
    | dimx == dimy = SP dimx (plus' x y)
    | otherwise = die "dim not equal!"
    where
        plus' :: (Num a) => [(Int, a)] -> [(Int, a)] -> [(Int, a)]
        plus' x_all@(c_x@(idx, x):xs) y_all@(c_y@(idy, y):ys) 
            | idx == idy = (idx, x + y) : plus' xs ys
            | idx < idy = c_x : plus' xs y_all
            | idx > idy = c_y : plus' x_all ys
        plus' xs ys = xs ++ ys

{-@ test2 :: SparseN Int 3 @-}
test2 :: Sparse Int
test2 = plus vec1 vec2
    where
        vec1 = SP 3 [(0, 12), (2, 9)]
        vec2 = SP 3 [(0, 8), (1, 100)]

{-@ data IncList a = 
    Emp
  | (:<) { hd :: a, tl :: IncList { v:a | hd <= v }} @-}
data IncList a =
    Emp
  | (:<) { hd :: a, tl :: IncList a }

infixr 9 :<

okList = 1 :< 2 :< 3 :< Emp

insertSort :: (Ord a) => [a] -> IncList a
insertSort [] = Emp
insertSort (x:xs) = insert x (insertSort xs)

insert :: (Ord a) => a -> IncList a -> IncList a
insert y Emp = y :< Emp
insert y (x :< xs)
    | y <= x = y :< x :< xs
    | otherwise = x :< insert y xs

