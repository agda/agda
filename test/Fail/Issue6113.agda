{-# OPTIONS --rewriting #-}

open import Agda.Builtin.Unit
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

X : Set

postulate
  ν : Set → Set → X
  ν-id : (P : Set) → ν P P ≡ tt  -- Jesper, 2022-10-19: unfixed #5600 so you now get an error here
  {-# REWRITE ν-id #-}

  μ : X → Set
  μ-unit-r : μ (ν X ⊤) ≡ ⊤
  {-# REWRITE μ-unit-r #-}

X = ⊤
