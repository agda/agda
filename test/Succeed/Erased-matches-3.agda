-- The option --erased-matches=empty enables erased matches for the
-- empty type.

{-# OPTIONS --erased-matches=empty #-}

data ⊥ : Set where

⊥-elim : ∀ {a} {@0 A : Set a} → @0 ⊥ → A
⊥-elim ()
