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

{-@ die :: {v:String | false} -> a @-}
die = error

{-@ zipWith1 :: (a->b->c) -> xs:List a -> ListX b xs -> ListX c xs @-}
zipWith1 f (a:as) (b:bs) = f a b : zipWith1 f as bs
zipWith1 _ [] [] = []
zipWith1 _ _ _ = die "no other cases"

{-@ zip1 :: as:[a] -> bs:[b] -> {v:[(a, b)] | Tinier v as bs }@-}
zip1 (a:as) (b:bs) = (a, b): zip1 as bs
zip1 [] _ = []
zip1 _ [] = []

{-@ predicate Tinier X Y Z = Min (size X) (size Y) (size Z) @-}
{-@ predicate Min X Y Z = (if Y < Z then X = Y else X = Z) @-}

-- exercise 6.3
{-@ zipOrNull :: xs: List a ->
    {ys: List b | (size xs /= 0 && size ys /= 0) => (size xs == size ys)} ->
    {v:List (a, b) | if (size xs == size ys) then (size v == size xs) else (size v == 0)} @-}

zipOrNull :: [a] -> [b] -> [(a, b)]
zipOrNull [] _ = []
zipOrNull _ [] = []
zipOrNull xs ys = zipWith1 (,) xs ys

{-@ test1 :: {v: _ | size v = 2} @-}
test1 = zipOrNull [0, 1] [True, False]

{-@ test2 :: {v: _ | size v = 0} @-}
test2 = zipOrNull [] [True, False]

{-@ test3 :: {v: _ | size v = 0} @-}
test3 = zipOrNull ["cat", "dog"] []


{-@ take' :: n:Nat -> ListGE a n -> ListN a n @-}
take' :: Int -> [a] -> [a]
take' 0 _ = []
take' n (x:xs) = x : take' (n - 1) xs
take' _ _ = die "won't happen"

{-@ type ListGE a N = {v:List a | N <= size v} @-}

-- exercise 6.4
{-@ drop' :: n:Nat -> xs:ListGE a n -> ListN a {size xs - n} @-}
drop' :: Int -> [a] -> [a]
drop' 0 xs = xs
drop' n (_:xs) = drop' (n - 1) xs
drop' _ _ = die "won't happen"

{-@ test4 :: ListN String 2 @-}
test4 = drop' 1 ["cat", "dog", "mouse"]

-- exercise 6.5
{-@ take'' :: n:Nat -> xs:List a -> ListN a {if n < (size xs) then n else (size xs)}@-}
take'' :: Int -> [a] -> [a]
take'' 0 _ = []
take'' _ [] = []
take'' n (x:xs) = x : take'' (n - 1) xs

{-@ test5 :: [ListN String 2] @-}
test5 = [ take'' 2 ["cat", "dog", "mouse"]
        , take'' 20 ["cow", "goat"]]

{-@ predicate Sum2 X N = (size (fst X) + size (snd X) == N && len (fst X) + len(snd X) == N) @-}
{-@ partition :: _ -> xs:_ -> {v:_ | Sum2 v (size xs)} @-}

partition :: (a -> Bool) -> [a] -> ([a], [a])
partition _ [] = ([], [])
partition f (x:xs)
  | f x = (x:ys, zs)
  | otherwise = (ys, x:zs)
  where
    (ys, zs) = partition f xs

{-@ pivApp :: a -> xs:[a] -> ys:[a] -> ListN a {size xs + size ys + 1} @-}
pivApp piv [] ys = piv : ys
pivApp piv (x:xs) ys = x : pivApp piv xs ys

{-@ measure fst @-}
{-@ measure snd @-}
fst (x,_) = x
snd (_,y) = y

-- exercise 6.6
{-@ quickSort' :: (Ord a) => xs:List a -> ListX a xs @-}
quickSort' :: (Ord a) => [a] -> [a]
quickSort' [] = []
quickSort' (x:xs) = let
  (l, r) = partition cmp xs
  cmp t = t < x in
    pivApp x l r

{-@ test10 :: ListN String 2 @-}
test10 :: [String]
test10 = quickSort' test4
