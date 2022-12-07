{-# OPTIONS --erasure #-}

postulate
  F : Set → Set
  _ : {@0 A : Set} → F λ { → A }
