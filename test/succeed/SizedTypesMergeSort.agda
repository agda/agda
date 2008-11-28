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

-- CPS split (non-size increasing)

split : {A : Set}{i : Size} -> List A {i} -> 
        {C : Set} -> (List A {i} -> List A {i} -> C) -> C
split []        k = k [] []
split (x :: xs) k = split xs (\ l r -> k (x :: r) l)


module Sort (A : Set) (compare : A -> A -> {B : Set} -> B -> B -> B) where

  -- Andreas, 4 Sep 2008
  -- the size indices i and j should not be necessary here
  -- but without them, the termination checker does not recognise that
  -- the pattern x :: xs is equal to the term x :: xs
  -- I suspect that _::_ {∞} x xs is not equal to itself since ∞ is a term
  -- not a constructor or variable
  merge : {i j : Size} -> List A {i} -> List A {j} -> List A
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
