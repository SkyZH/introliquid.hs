module Ex062 where

{-@ measure size @-}
{-@ size :: xs:[a] -> {v:Nat | v = size xs} @-}
size :: [a] -> Int
size [] = 0
size (_:rs) = 1 + size rs

type List a = [a]
{-@ type ListN a N = {v:List a | size v = N} @-}
{-@ type ListX a X = ListN a {size X} @-}

{-@ data Vector a = V { vDim :: Nat
                      , vElts :: ListN a vDim }@-}

{-@ vDim :: x:_ -> {v:Nat | v = vDim x} @-}


data Vector a = V { vDim :: Int
                  , vElts :: [a]
                  }
                deriving (Eq)

okVec = V 2 [10, 20]

{-@ type VectorNE a = {v:Vector a | vDim v > 0} @-}
{-@ type VectorN a N = {v:Vector a | vDim v = N} @-}
{-@ type VectorX a X = VectorN a {vDim X} @-}

{-@ vEmp :: VectorN a 0 @-}
vEmp = V 0 []

{-@ vCons :: a -> x:Vector a -> VectorN a {vDim x + 1} @-}
vCons x (V n xs) = V (n + 1) (x : xs)

{-@ vHd :: VectorNE a -> a @-}
vHd (V _ (x:_)) = x
vHd _ = die "nope"

{-@ die :: {v: String | false} -> a @-}
die = error

{-@ vTl :: x:VectorNE a -> VectorN a {vDim x - 1} @-}
vTl (V n (_:xs)) = V (n - 1) xs
vTl _ = die "nope"

{-@ for :: x:Vector a -> (a -> b) -> VectorX b x @-}
for (V n xs) f = V n (map1 f xs)

{-@ vBin :: (a -> b -> c) -> x:Vector a -> VectorX b x -> VectorX c x @-}
vBin op (V n xs) (V _ ys) = V n (zipWith1 op xs ys)

{-@ map1 :: (a->b) -> xs: List a -> ListX b xs @-}
map1 _ [] = []
map1 f (x:xs) = f x : map1 f xs

{-@ zipWith1 :: (a->b->c) -> xs:List a -> ListX b xs -> ListX c xs @-}
zipWith1 f (a:as) (b:bs) = f a b : zipWith1 f as bs
zipWith1 _ [] [] = []
zipWith1 _ _ _ = die "no other cases"

{-@ dotProduct :: (Num a) => x:Vector a -> VectorX a x -> a @-}
dotProduct x y = sum $ vElts $ vBin (*) x y

-- exercise 6.7
{-@ vecFromList :: xs:List a -> VectorN a {size xs} @-}
vecFromList :: List a -> Vector a
vecFromList xs = V (size xs) xs

test6 = dotProduct vx vy where
  vx = vecFromList [1,2,3]
  vy = vecFromList [4,5,6]
