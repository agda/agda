{-# OPTIONS --polarity #-}

module _ where

wrong : @++ Set → Set → Set
wrong A B = A → B
