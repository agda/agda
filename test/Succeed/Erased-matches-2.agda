-- One can give multiple options to --erased-matches. The different
-- options are combined.

{-# OPTIONS --erased-matches=empty,non-dependent,none #-}

data ⊥ : Set where

⊥-elim : ∀ {a} {@0 A : Set a} → @0 ⊥ → A
⊥-elim ()

data D : Set where
  c : D → D

F : @0 D → Set₁
F (c _) = Set
