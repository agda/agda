{-# OPTIONS --erasure #-}

postulate
  @0 A : Set

_ : (@0 B : Set) .(C : Set) → Set
_ = λ B C → ?
