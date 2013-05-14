module Issue847 where

data ⊥ : Set where

bad : ⊥
bad = bad′
  where
  abstract
    bad′ : ⊥
    bad′ = bad
