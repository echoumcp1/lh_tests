module No_abs_refine_list where

{-@ LIQUID "--exact-data-cons" @-}
{-@ reflect sorted @-}
{-@ sorted :: Ord a => [a] -> Bool @-}
sorted [] = True
sorted [x] = True
sorted (x:y:xs) = x <= y && sorted (y:xs)

type SList a = [a]
{-@ type SList a =  {v:[a] | sorted v} @-}

{-@ xs :: {v:SList Integer | len v = 1} @-}
xs = [1]