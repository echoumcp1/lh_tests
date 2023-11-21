{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--no-totality" @-}
module Trees where
import Prelude hiding (takeWhile)

data BalancedTree a = Leaf
           | Node { key :: a, left  :: BalancedTree a, right  :: BalancedTree a}
           deriving (Show)

{-@ type BalancedL a X = BalancedTree {v:a | v < X}  @-}
{-@ type BalancedR a X = BalancedTree {v:a | X < v}  @-}

{-@ measure realHeight @-}
realHeight :: BalancedTree a -> Int
realHeight Leaf         = 0
realHeight (Node _ l r) = 1 + max1 (realHeight l) (realHeight r)

{-@ inline max1 @-}
max1 :: Int -> Int -> Int
max1 x y = if x > y then x else y

{-@ inline isBal @-}
isBal l r n = negate n <= d && d <= n
  where
    d       = realHeight l - realHeight r

{-@ data BalancedTree a = Leaf
               | Node { key :: a
                      , left   :: BalancedL a key
                      , right  :: {v:BalancedR a key | isBal left v 1}}                                 
@-}

{-@ inOrder :: BalancedTree a -> [a] @-}
inOrder Leaf = []
inOrder (Node k l r) = inOrder l ++ [k] ++ inOrder r
                         
-- {-@ data Heap a = Empty
--                 | HeapNode {  rnk :: Int
--                             , val  :: a
--                             , lt    :: Heap {v:a | v < val} 
--                             , rt    :: Heap {v:a | v < val}} @-}

{-@ type OrderedList a = [a]<{\xi xj -> xi < xj}> @-}   

{-@ constructTree :: OrderedList a -> BalancedTree a @-}
constructTree [] = Leaf
constructTree xs = Node mid
                        (constructTree $ takeLess mid xs) 
                        (constructTree $ dropLessEq mid xs)
    where mid = xs !! (length xs `quot` 2)

{-@ takeLess :: k:a -> OrderedList a -> OrderedList {v:a | v < k} @-}
takeLess k [] = []
takeLess k (x:xs) 
  | x < k = x:takeLess k xs
  | otherwise = []

{-@ dropLessEq :: k:a -> OrderedList a -> OrderedList {v:a | v > k} @-}
dropLessEq k [] = []
dropLessEq k (x:xs)
  | x <= k = dropLessEq k xs
  | otherwise = xs
