{-# OPTIONS --rewriting #-}

open import Agda.Builtin.Unit
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

X : Set

postulate
  ν : Set → Set → X
  ν-id : (P : Set) → ν P P ≡ tt
  {-# REWRITE ν-id #-}

  μ : X → Set
  μ-unit-r : μ (ν X ⊤) ≡ ⊤
  {-# REWRITE μ-unit-r #-}

X = ⊤
