-- One can give --erased-matches multiple times. The different options
-- are combined.

{-# OPTIONS --erased-matches=empty
            --erased-matches=non-dependent
            --erased-matches=none
  #-}

data ⊥ : Set where

⊥-elim : ∀ {a} {@0 A : Set a} → @0 ⊥ → A
⊥-elim ()

data D : Set where
  c : D → D

F : @0 D → Set₁
F (c _) = Set
