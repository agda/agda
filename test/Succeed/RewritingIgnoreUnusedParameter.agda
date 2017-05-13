{-# OPTIONS --rewriting #-}

open import Agda.Builtin.Equality

postulate f : Set₁ → Set₁

module _ (A : Set) where
  postulate rew : f Set ≡ Set

{-# BUILTIN REWRITE _≡_ #-}
{-# REWRITE rew #-}
