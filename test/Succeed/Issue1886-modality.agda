{-# OPTIONS --erasure #-}

module _ where

data D (@erased A : Set) : Set

-- The modality should not be repeated here
data D (@erased A) where
  mkD : D A
