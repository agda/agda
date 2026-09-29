-- A test case for issue #8788.

{-# OPTIONS --erasure --erased-matches=none #-}

data ⊥ : Set where

record ⊥′ : Set where
  constructor c
  field
    impossible : ⊥

⊥′-elim : {@0 A : Set} → @0 ⊥′ → A
⊥′-elim = λ ()
