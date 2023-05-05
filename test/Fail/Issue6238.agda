{-
  Matching on @♭ is disallowed by default when --cubical is given (but
  see the Succeed/Issue6238, you can enable it; it isn't --safe to do
  so!)
-}
{-# OPTIONS --cubical --cohesion #-}
module Issue6238 where

data Flat (@♭ A : Set) : Set where
    flat : (@♭ a : A) → Flat A

data Id {A : Set} : A → A → Set where
  refl : {x : A} → Id x x

CommFlatId : {@♭ A : Set} {@♭ u v : A} → Flat (Id u v) → Id (flat u) (flat v)
CommFlatId (flat refl) = refl
