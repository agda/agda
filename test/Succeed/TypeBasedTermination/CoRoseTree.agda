-- Tests a coinductive rose tree
{-# OPTIONS --type-based-termination --no-syntax-based-termination #-}

module TypeBasedTermination.CoRoseTree where

data List (A : Set) : Set where
  nil : List A
  cons : A → List A → List A

map : {A B : Set} → (A → B) → List A → List B
map f nil = nil
map f (cons x xs) = cons (f x) (map f xs)

record CoRoseTree (A : Set) : Set where
  coinductive
  field
    ghd : A
    gtl : List (CoRoseTree A)

open CoRoseTree

gmap : {A B : Set} (f : A → B) → CoRoseTree A → CoRoseTree B
ghd (gmap f s) = f (ghd s)
gtl (gmap f s) = map (gmap f) (gtl s)
