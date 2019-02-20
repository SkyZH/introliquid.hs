module Ex062 where

{-@ measure len @-}
{-@ len :: xs:[a] -> {v:Nat | v = len xs} @-}
len :: [a] -> Int
len [] = 0
len (_:rs) = 1 + len rs

type List a = [a]
{-@ type ListN a N = {v:List a | len v = N} @-}
{-@ type ListX a X = ListN a {len X} @-}

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
{-@ vecFromList :: xs:List a -> VectorN a {len xs} @-}
vecFromList :: List a -> Vector a
vecFromList xs = V (len xs) xs

test6 = dotProduct vx vy where
  vx = vecFromList [1,2,3]
  vy = vecFromList [4,5,6]

{-@ flatten :: n:Nat -> m:Nat -> VectorN (VectorN a m) n -> VectorN a {m * n} @-}
flatten n m v = V (n * m) (flatten' (vElts v)) where
  {-@ flatten' :: xs:[VectorN a m] -> ListN a {m * (len xs)} @-}
  flatten' :: [Vector a] -> [a]
  flatten' (v:vs) = vElts v ++ flatten' vs
  flatten' _ = []

{-@ product :: xs:Vector _ -> ys:Vector _ -> VectorN _ {vDim xs * vDim ys} @-}
product xs ys = flatten (vDim ys) (vDim xs) xys where
  xys = for ys $ \y ->
    for xs $ \x -> x * y

{-@ data Matrix a =
    M { mRow :: Pos
      , mCol :: Pos
      , mElts :: VectorN (VectorN a mCol) mRow
      }
@-}

{-@ type Pos = {v:Int | 0 < v} @-}

data Matrix a = M { mRow :: Int
                  , mCol :: Int
                  , mElts :: Vector (Vector a)
                  }

{-@ type MatrixN a R C = {v:Matrix a | Dims v R C} @-}
{-@ predicate Dims M R C = mRow M = R && mCol M = C @-}

{-@ ok23 :: MatrixN _ 2 3 @-}
ok23 = M 2 3 (V 2 [ V 3 [1, 2, 3]
                  , V 3 [4, 5, 6] ])

-- exercise 6.10
{-
matFromList :: [[a]] -> Maybe (Matrix a)
matFromList [] = Nothing
matFromList xss@(xs:_)
  | ok = let
      vs = V r vcol
      vcol = map' (\x -> V c x) xss
      in Just $ M r c vs
  | otherwise = Nothing where
      r = len xss
      c = len xs
      ok = r > 0 && c > 0 && all' (\x -> len x == c) xss

{-@ map' :: (a -> b) -> xs:List a -> ListX b xs @-}
map' :: (a -> b) -> [a] -> [b]
map' f (x:xs) = f x : map' f xs
map' _ _ = []

{-@ all' :: (a -> Bool) -> [a] -> Bool @-}
all' :: (a -> Bool) -> [a] -> Bool
all' f (x:xs) = f x && all' f xs
all' _ _ = True

{-@ mat23 :: Maybe (MatrixN Int 2 2) @-}
mat23 :: Maybe (Matrix Int)
mat23 = matFromList [[1,2], [3,4]]
-}

