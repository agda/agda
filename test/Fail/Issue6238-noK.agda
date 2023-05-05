{-# OPTIONS --without-K --safe --cohesion #-}
module Issue6238-noK where

data Flat (@♭ A : Set) : Set where
    flat : (@♭ a : A) → Flat A

data Id {A : Set} : A → A → Set where
  refl : {x : A} → Id x x

CommFlatId : {@♭ A : Set} {@♭ u v : A} → Flat (Id u v) → Id (flat u) (flat v)
CommFlatId (flat refl) = refl
