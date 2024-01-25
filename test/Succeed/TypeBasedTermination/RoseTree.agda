-- test for map on rose trees
{-# OPTIONS --type-based-termination --no-syntax-based-termination #-}

module TypeBasedTermination.RoseTree where

data List (A : Set) : Set where
  nil  : List A
  cons : A → List A → List A

map : ∀ {A B} → (A → B) → List A → List B
map f nil         = nil
map f (cons a as) = cons (f a) (map f as)

data Rose (A : Set) : Set where
  rose : A → List (Rose A) → Rose A

mapRose : ∀ {A B} → (A → B) → Rose A → Rose B
-- usual termination checker cannot deduce decrease in structure for a recursive call, since this `mapRose f` is not fully applied.
-- on the contrary, in the presence of size-preserving map, we can learn that mapRose is a recursive call with a smaller size parameter
mapRose f (rose a rs) = rose (f a) (map (mapRose f) rs)
