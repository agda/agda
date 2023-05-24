{-# OPTIONS --forced-argument-recursion --no-large-indices --safe #-}
module Issue6654a where

-- Fails: to have safe forced argument recursion, large indices can not
-- be used, so the defn of Bad is rejected

data ⊥ : Set where

data Bad : ((P : Set) → P → P) → Set where
  b : (f : (P : Set) → P → P) → Bad f

bad : Bad _
bad = b λ P p → p

no-bad : ∀ {x} → Bad x → ⊥
no-bad (b x) = no-bad (x _ bad)

very-bad : ⊥
very-bad = no-bad bad
