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
{-@ type ListSub a X = {v:[a] | Set_sub (elts v (elts X))} @-}
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
