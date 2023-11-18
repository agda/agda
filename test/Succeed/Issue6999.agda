{-# OPTIONS --erasure #-}

postulate
  f : (P : @0 Set → Set₁) → (A : Set) → P A

fails : (A : Set) → @0 A → Set
fails = f _
