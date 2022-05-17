{- Example by Andreas (2015-09-18) -}
{- Jesper, 2021-03-19: Since the fix of #5238 this example is no longer allowed -}

{-# OPTIONS --rewriting --local-confluence-check #-}

open import Common.Prelude
open import Common.Equality

{-# BUILTIN REWRITE _≡_ #-}

module _ (A : Set) where

  postulate
    plus0p :  ∀{x} → (x + zero) ≡ x

  {-# REWRITE plus0p #-}
