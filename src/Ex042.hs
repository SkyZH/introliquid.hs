{-@ LIQUID "--short-names"         @-}
{-@ LIQUID "--no-termination"      @-}
{-@ LIQUID "--scrape-used-imports" @-}
module Ex042
        ( Sparse(..)
        , IncList(..)
        , dotProd
        , dotProd'
        , fromList
        , test1
        , plus
        , test2
        , insert
        , insertSort
        , insertSort'
        , merge
        , split
        , mergeSort
        , BST(..)
        , mem
        , add
        )
where

import           Data.List                      ( foldl' )
import           Data.Maybe
import           Data.Vector             hiding ( all
                                                , foldl'
                                                , foldr
                                                , fromList
                                                , head
                                                , (++)
                                                )
import           Prelude                 hiding ( abs
                                                , head
                                                , length
                                                )

{-@ type Btwn Lo Hi = {v:Int | Lo <= v && v < Hi} @-}

{-@ data Sparse a = SP { spDim :: Nat
                       , spElems :: [(Btwn 0 spDim, a)]} @-}
data Sparse a = SP { spDim   :: Int
                   , spElems :: [(Int, a)]}

okSP :: Sparse String
okSP = SP 5 [(0, "cat"), (3, "dog")]

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
        where body sum (i, v) = sum + (x ! i) * v

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
plus (SP dimx x) (SP dimy y) | dimx == dimy = SP dimx (plus' x y)
                             | otherwise    = die "dim not equal!"
    where
        plus' :: (Num a) => [(Int, a)] -> [(Int, a)] -> [(Int, a)]
        plus' x_all@(c_x@(idx, x) : xs) y_all@(c_y@(idy, y) : ys)
                | idx == idy = (idx, x + y) : plus' xs ys
                | idx < idy  = c_x : plus' xs y_all
                | idx > idy  = c_y : plus' x_all ys
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

infixr 9 :<
data IncList a =
    Emp
  | (:<) { hd :: a, tl :: IncList a }
  deriving(Show)


okList = 1 :< 2 :< 3 :< Emp

insertSort :: (Ord a) => [a] -> IncList a
insertSort []       = Emp
insertSort (x : xs) = insert x (insertSort xs)

insert :: (Ord a) => a -> IncList a -> IncList a
insert y Emp = y :< Emp
insert y (x :< xs) | y <= x    = y :< x :< xs
                   | otherwise = x :< insert y xs


-- exercise 4.11
insertSort' :: (Ord a) => [a] -> IncList a
insertSort' xs = foldr f b xs
    where
        f x xs = insert x xs
        b = Emp

split :: [a] -> ([a], [a])
split (x : y : zs) = (x : xs, y : ys) where (xs, ys) = split zs
split xs           = (xs, [])

merge :: (Ord a) => IncList a -> IncList a -> IncList a
merge Emp ys  = ys
merge xs  Emp = xs
merge (x :< xs) (y :< ys) | x <= y    = x :< (merge xs (y :< ys))
                          | otherwise = y :< (merge (x :< xs) ys)
merge _ _ = Emp

mergeSort :: (Ord a) => [a] -> IncList a
mergeSort []  = Emp
mergeSort [x] = x :< Emp
mergeSort xs  = merge (mergeSort ys) (mergeSort zs) where (ys, zs) = split xs

{-@ data BST a = Leaf
               | Node { root :: a
                      , left :: BSTL a root
                      , right :: BSTR a root } @-}
{-@ type BSTL a X = BST { v:a | v < X} @-}
{-@ type BSTR a X = BST {v:a | X < v} @-}

data BST a = Leaf
           | Node { root  :: a
                  , left  :: BST a
                  , right :: BST a }

okBST :: BST Int
okBST = Node 6
             (Node 2 (Node 1 Leaf Leaf) (Node 4 Leaf Leaf))
             (Node 9 (Node 7 Leaf Leaf) Leaf)

-- exercise 4.13
-- no it can't


mem :: (Ord a) => a -> BST a -> Bool
mem _ Leaf = False
mem k (Node k' l r) | k == k'   = True
                    | k < k'    = mem k l
                    | otherwise = mem k r

one :: a -> BST a
one x = Node x Leaf Leaf

add :: (Ord a) => a -> BST a -> BST a
add k' Leaf = one k'
add k' t@(Node k l r) | k' < k    = Node k (add k' l) r
                      | k < k'    = Node k l (add k' r)
                      | otherwise = t
{-
data MinPair a = MP { mElt :: a, rest :: BST a }
{-@ data MinPair a = MP { mElt :: a, rest :: BSTR a mElt} @-}
delMin :: (Ord a) => BST a -> MinPair a
delMin (Node k Leaf r) = MP k r
delMin (Node k l r) = MP k' (Node k l' r)
    where
        MP k' l' = delMin l
delMin Leaf = die "Don't say I didn't warn ya!"

del :: (Ord a) => a -> BST a -> BST a
del k' t@(Node k l r)
    | k' /= k = t
    | k' == k = Node re (del k' l) rt
        where
            MP re rt = delMin r
del _ Leaf = Leaf
-}
