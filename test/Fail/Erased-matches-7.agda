-- The flag --erased-matches can be overridden by --erased-matches=X.

{-# OPTIONS --erased-matches --erased-matches=none #-}

data ⊥ : Set where

⊥-elim : ∀ {a} {@0 A : Set a} → @0 ⊥ → A
⊥-elim ()
