{-
  Example for matching on a flatted variable from an inductive family (Issue #6238).
-}
{-# OPTIONS --cubical --flat-split -WnoUnsupportedIndexedMatch #-}
module Issue6238 where

data Flat (@♭ A : Set) : Set where
    flat : (@♭ a : A) → Flat A

data Id {A : Set} : A → A → Set where
  refl : {x : A} → Id x x

CommFlatId : {@♭ A : Set} {@♭ u v : A} → Flat (Id u v) → Id (flat u) (flat v)
CommFlatId (flat refl) = refl
