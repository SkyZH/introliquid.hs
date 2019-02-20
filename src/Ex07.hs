module Ex07 where

import Data.Set hiding (insert, partition, filter, split, elems)
import Prelude  hiding (elem, reverse, filter)


{-@ type True = {v:Bool | v} @-}
{-@ type False = {v:Bool | not v} @-}

{-@ prop_one_plus_one_eq_two :: _ -> True @-}
prop_one_plus_one_eq_two x = (x == 1 + 1) `implies` (x == 2)

{-@ implies :: p:Bool -> q:Bool -> Implies p q @-}
implies False _ = True
implies _ True = True
implies _ _ = False

{-@ type Implies P Q = {v:_ | v <=> (P => Q)} @-}

-- exercise 7.1
{-@ prop_x_y_200 :: _ -> _ -> True @-}
prop_x_y_200 x y = ((x < 100) && (y < 100)) `implies` (x + y < 200)


{-@ prop_intersection_comm :: _ -> _ -> True @-}
prop_intersection_comm x y
  = (x `intersection` y) == (y `intersection` x)

{-@ prop_union_assoc :: _ -> _ -> _ -> True @-}
prop_union_assoc x y z
  = (x `union` (y `union` z)) == (x `union` y) `union` z

{-@ prop_intersection_dist :: _ -> _ -> _ -> True @-}
prop_intersection_dist x y z =
  x `intersection` (y `union` z) == (x `intersection` y) `union` (x `intersection` z)

-- exercise 7.2
{-@ prop_cup_dif_bad :: _ -> _ -> True @-}
prop_cup_dif_bad x y =
  pre `implies` (x == ((x `union` y) `difference` y)) where
  pre = x == empty

{-@ measure elts @-}
elts :: (Ord a) => [a] -> Set a
elts [] = empty
elts (x:xs) = singleton x `union` elts xs

{-@ type ListS a S = {v:[a] | elts v = S} @-}
{-@ type ListEmp a = ListS a {Set_empty 0} @-}
{-@ type ListEq a X = ListS a {elts X} @-}
{-@ type ListSub a X = {v:[a] | Set_sub (elts v) (elts X)} @-}
{-@ type ListUn a X Y = ListS a {Set_cup (elts X) (elts Y)} @-}
{-@ type ListUn1 a X Y = ListS a {Set_cup (Set_sng X) (elts Y)} @-}

{-@ append' :: xs:_ -> ys:_ -> ListUn a xs ys @-}
append' [] ys = ys
append' (x:xs) ys = x : append' xs ys

type List a = [a]

-- exercise 7.3
{-@ reverse' :: xs:List a -> ListEq a xs @-}
reverse' xs = revHelper [] xs where
  {-@ revHelper :: xs:List a -> ys:List a -> ListUn a xs ys @-}
  revHelper acc [] = acc
  revHelper acc (x:xs) = revHelper (x:acc) xs

-- exercise 7.5

{-@ elem' :: (Eq a) => x:a -> xs:[a] -> {v:Bool | v <=> Set_mem x (elts xs)} @-}
elem' x (y:ys) = x == y || elem' x ys
elem' _ [] = False

{-@ test1 :: True @-}
test1 = elem' 2 [1, 2, 3]

{-@ test2 :: False @-}
test2 = elem' 2 [1, 3]

insert x [] = [x]
insert x (y:ys)
  | x <= y = x : y : ys
  | otherwise = y : insert x ys
{-@ insert :: x:a -> xs:List a -> ListUn1 a x xs @-}

{-@ insertSort :: (Ord a) => xs:List a -> ListEq a xs @-}
insertSort [] = []
insertSort (x:xs) = insert x (insertSort xs)

{-@ measure unique @-}
unique :: (Ord a) => List a -> Bool
unique [] = True
unique (x:xs) = unique xs && not (member x (elts xs))

{-@ type UList a = {v:List a | unique v} @-}
{-@ isUnique :: UList Int @-}
isUnique :: [Int]
isUnique = [1, 2, 3]
 

{-@ filter' :: (a -> Bool) -> xs:UList a -> {v:ListSub a xs | unique v} @-}

filter' _ [] = []
filter' f (x:xs)
  | f x = x : xs'
  | otherwise = xs' where
      xs' = filter' f xs

-- exercise 7.8
{-@ filter'' :: (a -> Bool) -> xs:List a -> {v:ListSub a xs | unique xs => unique v} @-}
filter'' _ [] = []
filter'' f (x:xs)
  | f x = x : xs'
  | otherwise = xs' where
      xs' = filter'' f xs

{-@ test3 :: UList _ @-}
test3 :: [Int]
test3 = filter'' (> 2) [1, 2, 3, 4]

{-@ test4 :: [_] @-}
test4 :: [Int]
test4 = filter'' (> 3) [3, 1, 2, 3]

{-@ nub :: List a -> UList a @-}
nub xs = go [] xs where
  go seen [] = seen
  go seen (x:xs)
    | x `isin` seen = go seen xs
    | otherwise = go (x:seen) xs

{-@ predicate In X Xs = Set_mem X (elts Xs) @-}

{-@ isin :: x:_ -> ys:_ -> {v:Bool | v <=> In x ys} @-}
isin x (y:ys)
  | x == y = True
  | otherwise = x `isin` ys

isin _ [] = False
