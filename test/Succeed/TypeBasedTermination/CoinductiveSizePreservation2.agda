-- Tests a case of coinductive size preservation 2
{-# OPTIONS --type-based-termination --no-syntax-based-termination #-}

module TypeBasedTermination.CoinductiveSizePreservation2 where

record Bush (A : Set) : Set where
  coinductive
  field
    head : A
    tail : Bush (Bush A)

open Bush

map : {A B : Set} → (A → B) → Bush A → Bush B
map f b .head = f (b .head)
map f b .tail = map (map f) (b .tail)
