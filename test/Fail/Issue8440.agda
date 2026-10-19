{-# OPTIONS --cubical #-}
module Issue8440 where

open import Agda.Primitive.Cubical
  renaming ( primINeg       to infix  30 ~_   -- I → I
           ; primIMin       to infixr 20 _∧_  -- I → I → I
           ; primIMax       to infixr 20 _∨_  -- I → I → I
           )

data Wrap (A : Set) : Set where
  wrap : A → Wrap A

test : (A : Set) (w : Wrap A) (i : I) → Partial (i ∨ ~ i) A
test A (wrap a) i p = a
