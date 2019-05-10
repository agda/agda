{- Example by Andreas (2015-09-18) -}

{-# OPTIONS --rewriting --confluence-check #-}

open import Common.Prelude
open import Common.Equality

{-# BUILTIN REWRITE _≡_ #-}

module _ (A : Set) where

  postulate
    plus0p :  ∀{x} → (x + zero) ≡ x

  {-# REWRITE plus0p #-}
