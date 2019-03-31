{-@ LIQUID "--no-termination" @-}

module Case01 where

import Prelude hiding (replicate)

data SList a  = SL { size:: Int
                   , elems:: [a]
                   }

{-@ data SList a = SL { size :: Nat
                      , elems :: {v:[a] | len v = size}
                      } @-}

{-@ type SListN a N = {v:SList a | size v = N} @-}

{-@ nil :: SListN a 0 @-}
nil = SL 0 []

{-@ cons :: a -> xs:SList a -> SListN a {size xs + 1} @-}
cons x (SL n xs) = SL (n + 1) (x:xs)

{-@ die :: {v:String | false} -> a @-}
die = error

{-@ tl :: {xs:SList a | size xs >= 1} -> SListN a {size xs - 1} @-}
tl (SL n (_:xs)) = SL (n-1) xs
tl _ = die "empty SList"

{-@ hd :: {xs:SList a | size xs >= 1} -> a @-}
hd (SL _ (x:_)) = x
hd _ = die "empty SList"

{-@ data Queue a = Q { front :: SList a
                     , back :: SListLE a (size front)
                     } @-}

data Queue a = Q { front :: SList a
                 , back :: SList a
                 }
{-@ type SListLE a N = {v:SList a | size v <= N } @-}

{-@ measure qSize @-}
qSize (Q f b) = size f + size b

{-@ type QueueN a N = {v:Queue a | qSize v = N} @-}

{-@ emp :: QueueN a 0 @-}
emp = Q nil nil

{-@ remove :: {v:Queue a | qSize v > 0} -> (a, QueueN a {qSize v - 1}) @-}
remove :: Queue a -> (a, Queue a)
remove (Q f b) = (hd f, makeq (tl f) b)

{-@ insert :: a -> v:Queue a -> QueueN a {qSize v + 1} @-}
insert :: a -> Queue a -> Queue a
insert e (Q f b) = makeq f (e `cons` b)

{-@ replicate :: n:Nat -> a -> QueueN a n @-}
replicate :: Int -> a -> Queue a
replicate 0 _ = emp
replicate n x = insert x (replicate (n - 1) x)

{-@ makeq :: f:SList a -> {b:SList a | size b <= size f + 1} -> QueueN a {size f + size b} @-}
makeq f b
  | size b <= size f = Q f b
  | otherwise = Q (rot f b nil) nil

{-@ rot :: f:SList t -> {b:SList t | size b = size f + 1} -> a:SList t -> {v:SList t | size v = size f + size b} @-}
rot :: SList a -> SList a -> SList a -> SList a
rot = undefined
{-  
rot :: SList a -> SList a -> SList a -> SList a
rot f b a
  | size f == 0 = hd b `cons` a
  | otherwise = hd f `cons` rot (tl f) (tl b) (hd b `cons` a)
-}
