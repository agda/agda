F : Set₁
F = Set
  -- Everything in the where module is erased.
  module @0 G where
    H : @0 Set → Set
    H A = A

_ : @0 Set → Set
_ = G.H
