module Okasaki where
{-@ LIQUID "--no-termination" @-}

import Prelude hiding (min)
import Control.Monad.Trans.State ( State, evalState, get, put )
import Control.Monad
{-@ data LH a =
      E |
      T
        (r     :: {v:Nat | v > 0})
        (left  :: LH a)
        (right :: {v:LH a | (rank v == r - 1) &&
                            (rank left >= rank v)})
        (val   :: {v:a | IsMin v left && IsMin v right} )
  @-}

data LH a = E | T Int (LH a) (LH a) a deriving (Show)

{-@ predicate IsEmptyLH H = tsize H == 0 @-}
{-@ predicate IsMin N H = IsEmptyLH H || N <= (hmin H) @-}

{-@ measure hmin @-}
{-@ hmin :: forall a. {v:LH a | tsize v /= 0} -> a @-}
hmin (T _ _ _  v) = v

{-@ measure rank @-}
{-@ rank :: LH a -> Nat @-}
rank E           = 0
rank (T r _ _ _) = r

{-@ makeT :: forall a.
      l:LH a                         ->
      r:LH a                         ->
      v:{a | IsMin v l && IsMin v r} ->
      {h:LH a | IsMin v h && (tsize h) == 1 + (tsize l) + (tsize r)}
@-}

makeT :: LH a -> LH a -> a -> LH a
makeT l r v
  | rank l >= rank r = T (1 + rank r) l r v
  | otherwise        = T (1 + rank l) r l v

{-@ measure tsize @-}
{-@ tsize :: forall a.
      LH a ->
      Nat
  @-}
tsize :: LH a -> Int
tsize E           = 0
tsize (T _ l r _) = 1 + (tsize l) + (tsize r)

{-@ isEmpty :: forall a. Ord a =>
      h:LH a ->
      {v:Bool | v <=> (0 == tsize h)} @-}
isEmpty E = True
isEmpty _ = False

{-@ findMin :: 
      {h:LH a | tsize h /= 0} ->
      {v:a | IsMin v h}
  @-}
{-@ measure findMin @-}
findMin h@(T _ _ _ v) = v

{-@ mergeAux :: Ord a =>
      e:a ->
      h0:LH a ->
      h1:LH a ->
      {h2:LH a | (tsize h2 == tsize h0 + tsize h1) &&
                 ((IsMin e h0 ==> IsMin e h2) || (IsMin e h1 ==> IsMin e h2))}
  @-}
mergeAux :: Ord a => a -> LH a -> LH a -> LH a
mergeAux _ h E = h
mergeAux _ E h = h
mergeAux e
      h1@(T _ a1 b1 v1)
      h2@(T _ a2 b2 v2)
      | v1 <= v2    = makeT a1 (mergeAux v1 b1 h2) v1
      | otherwise = makeT a2 (mergeAux v2 h1 b2) v2

{-@ merge :: forall a. Ord a =>
      h0:LH a ->
      h1:LH a ->
      {h2:LH a | (tsize h2 == tsize h0 + tsize h1)}
  @-}
merge :: Ord a => LH a -> LH a -> LH a
merge E E = E
merge h0@(T _ _ _ x) h1 = mergeAux x h0 h1
merge h0 h1@(T _ _ _ y) = mergeAux y h0 h1

-- merge E heap = heap
-- merge heap E = heap
-- merge h1@(T _ left1 right1 x)
--       h2@(T _ left2 right2 y) =
--   if x > y
--     then makeT left1 (merge right1 h2) x
--     else makeT left2 (merge right2 h1) y

{-@ insert :: forall a. Ord a =>
      a ->
      h0:LH a ->
      {h1:LH a | tsize h1 == tsize h0 + 1}
@-}

insert v h = merge (T 1 E E v) h

{-@ deleteMin :: forall a. Ord a =>
      {h0:LH a | tsize h0 /= 0} ->
      {h1:LH a | tsize h1 == tsize h0 - 1}
  @-}
deleteMin (T _ r l v) = merge r l

{-@ type OrderedList a = [a]<{\xi xj -> xi <= xj}> @-}

{-@ heapify :: [a] -> LH a @-}
heapify :: Ord a => [a] -> LH a
heapify = foldl (flip insert) E

-- {-@ heapsort :: forall a. Ord a =>
--       h:LH a ->
--       {xs:OrderedList a | (tsize h == len xs)}
--   @-}
heapsort :: Ord a => LH a -> [a]
heapsort heap =
  case heap of
    E -> []
    (T _ _ _ v) -> findMin heap : heapsort (deleteMin heap)


{-@ test :: OrderedList Integer @-}
test :: [Integer]
test = []