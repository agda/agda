{-# OPTIONS --erasure #-}

data ⊥ : Set where

_ : @0 ⊥ → Set
_ = λ @0 { () }
