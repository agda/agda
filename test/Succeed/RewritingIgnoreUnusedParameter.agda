{-# OPTIONS --rewriting --confluence-check #-}

open import Agda.Builtin.Equality

postulate f : Set₁ → Set₁

module _ (A : Set) where
  postulate rew : f Set ≡ Set

{-# BUILTIN REWRITE _≡_ #-}
{-# REWRITE rew #-}
{- Jesper, 2021-03-19: Since the fix of #5238 this example is no longer allowed -}
