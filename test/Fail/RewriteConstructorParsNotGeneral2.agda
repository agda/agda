{-# OPTIONS --rewriting #-}

open import Agda.Builtin.Bool
open import Agda.Builtin.Equality
{-# BUILTIN REWRITE _≡_ #-}

data D (A : Set) : Set where
  c c' : D A

module M (A : Set) where

  postulate rew : c {A} ≡ c' {A}

  {-# REWRITE rew #-}

  test : ∀ {B} → c {B} ≡ c' {B}
  test = refl
