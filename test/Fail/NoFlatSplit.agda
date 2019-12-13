{-# OPTIONS --no-flat-split #-}
module _ where

postulate
  A : Set

data Id (A : Set) : Set where
  id : A → Id A

-- --no-flat-split disables matching on the @♭ x agument.
test2 : (@♭ x : Id A) → A
test2 (id x) = x
