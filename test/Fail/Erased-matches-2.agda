-- The option --erased-matches=unrestricted does not enable erased
-- matches for empty types.

{-# OPTIONS --erased-matches=unrestricted #-}

data ⊥ : Set where

⊥-elim : ∀ {a} {@0 A : Set a} → @0 ⊥ → A
⊥-elim ()
