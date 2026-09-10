-- If the K rule is off, then --erased-matches without options enables
-- erased matches for empty types and non-indexed, single-constructor
-- data types.

{-# OPTIONS --without-K --erased-matches #-}

data ⊥ : Set where

⊥-elim : ∀ {a} {@0 A : Set a} → @0 ⊥ → A
⊥-elim ()

data D : Set where
  c : D → D

F : @0 D → Set₁
F (c _) = Set
