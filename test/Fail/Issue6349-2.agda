{-# OPTIONS --without-K --erasure #-}

data Unit : Set where
  unit : Unit

f : @0 Unit → Unit
f unit = unit
