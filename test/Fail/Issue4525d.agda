{-# OPTIONS --erasure #-}

postulate
  F : @0 Set → Set

G : @0 Set → Set
G A = F (λ { → A })
