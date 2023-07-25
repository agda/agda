{-# OPTIONS --with-K --large-indices --no-forced-argument-recursion --safe #-}
module Issue6654b where

-- Fails: we asked for large indices and no forced argument recursion, so the
-- termination checker complains about no-bad

data ⊥ : Set where

data Bad : ((P : Set) → P → P) → Set where
  b : (f : (P : Set) → P → P) → Bad f

bad : Bad _
bad = b λ P p → p

no-bad : ∀ {x} → Bad x → ⊥
no-bad (b x) = no-bad (x _ bad)

very-bad : ⊥
very-bad = no-bad bad
