{-# OPTIONS --sized-types #-}

module SizedTypesMergeSort where

postulate
  Size : Set
  _^   : Size -> Size
  ∞    : Size

{-# BUILTIN SIZE Size  #-}
{-# BUILTIN SIZESUC _^ #-}
{-# BUILTIN SIZEINF ∞  #-}

-- sized lists

data List (A : Set) : {_ : Size} -> Set where
  []   : {size : Size} -> List A {size ^}
  _::_ : {size : Size} -> A -> List A {size} -> List A {size ^}

-- CPS split

split : {A : Set}{i : Size} -> List A {i} -> 
        {C : Set} -> (List A {i} -> List A {i} -> C) -> C
split []        k = k [] []
split (x :: xs) k = split xs (\ l r -> k (x :: r) l)


module Sort (A : Set) (compare : A -> A -> {B : Set} -> B -> B -> B) where

{- merge is currently rejected by the termination checker
   it would be nice if it worked
   see test/succeed/SizedTypesMergeSort.agda
 -}
  merge : List A -> List A -> List A
  merge [] ys = ys
  merge xs [] = xs
  merge (x :: xs) (y :: ys) = 
    compare x y (x :: merge xs (y :: ys))
                (y :: merge (x :: xs) ys) 

  sort : {i : Size} -> List A {i} -> List A
  sort [] = []
  sort (x :: []) = x :: []
  sort (x :: (y :: xs)) = split xs (\ l r -> merge (sort (x :: l)) 
                                                   (sort (y :: r)))
