{-# OPTIONS --erasure #-}

postulate
  @0 A : Set

_ : @0 Set → (Set → Set) → Set
_ = λ @0 where
  A G → G A
