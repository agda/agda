{-# OPTIONS --cubical #-}
module Issue8440 where

open import Agda.Primitive.Cubical
  renaming ( primIMin       to _∧_  -- I → I → I
           ; primIMax       to _∨_  -- I → I → I
           ; primINeg       to ~_   -- I → I
           )

data Wrap (A : Set) : Set where
  wrap : A → Wrap A

test : (A : Set) (w : Wrap A) (i : I) → Partial (i ∨ ~ i) A
test A (wrap a) i p = a
