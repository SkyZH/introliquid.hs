module Ex06 where

{-@ measure size @-}
{-@ size :: xs:[a] -> {v:Nat | v = size xs} @-}
size :: [a] -> Int
size [] = 0
size (_:rs) = 1 + size rs

{-@ measure notEmpty @-}
notEmpty :: [a] -> Bool
notEmpty [] = False
notEmpty (_:_) = True

data Vector a = V { vDim :: Int
                  , vElts :: [a]
                  }
                deriving (Eq)

data Matrix a = M { mRow :: Int
                  , mCol :: Int
                  , mElts :: Vector (Vector a)
                  }
                deriving (Eq)

dotProd :: (Num a) => Vector a -> Vector a -> a
dotProd vx vy = sum (prod xs ys)
  where
    prod = zipWith(\x y -> x * y)
    xs = vElts vx
    ys = vElts vy

matProd :: (Num a) => Matrix a -> Matrix a -> Matrix a
matProd (M rx _ xs) (M _ cy ys) = M rx cy elts where
  elts = for xs $ \xi ->
                    for ys $ \yj ->
                               dotProd xi yj

for :: Vector a -> (a -> b) -> Vector b
for (V n xs) f = V n (map f xs)

type List a = [a]
{-@ type ListN a N = {v:List a | size v = N} @-}
{-@ type ListX a X = ListN a {size X} @-}

-- exercise 6.1

{-@ type TRUE  = {v:Bool | v    } @-}
{-@ type FALSE = {v:Bool | not v} @-}

{-@ map1 :: (a->b) -> xs: List a -> ListX b xs @-}
map1 _ [] = []
map1 f (x:xs) = f x : map1 f xs

{-@ prop_map :: List a -> TRUE @-}
prop_map xs = size ys == size xs where
  ys = map1 id xs

-- exercise 6.2
{-@ reverse :: xs: List a -> ListX a xs @-}
reverse xs = go [] xs where
  {-@ go :: left: List a -> right: List a -> ListN a {(size left) + (size right)} @-}
  go acc [] = acc
  go acc (x:xs) = go (x:acc) xs
  
