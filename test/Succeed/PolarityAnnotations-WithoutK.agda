{-# OPTIONS --polarity --without-K #-}
module _ where

record PosPair (@++ X : Set) (Y : Set) : Set where
  field
    fst : X
    snd : Y
