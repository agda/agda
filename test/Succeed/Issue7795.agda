{-# OPTIONS --polarity #-}
module Issue7795 where

data Box (@++ A : Set) : Set where
  [_] : A → Box A

opaque
  Box′ : @++ Set → Set
  Box′ A = Box A

data D : Set where
  c : Box′ D → D
