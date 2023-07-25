{-# OPTIONS --forced-argument-recursion --large-indices --safe #-}
module Issue6654c where

-- Fails: having both of these options would allow the program to go
-- through, but they're not --safe together

data ⊥ : Set where

data Bad : ((P : Set) → P → P) → Set where
  b : (f : (P : Set) → P → P) → Bad f

bad : Bad _
bad = b λ P p → p

no-bad : ∀ {x} → Bad x → ⊥
no-bad (b x) = no-bad (x _ bad)

very-bad : ⊥
very-bad = no-bad bad
