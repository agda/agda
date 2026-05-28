{-# OPTIONS --erasure #-}

open import Agda.Builtin.Sigma

Works : Set₁
Works = Σ _ λ (_ : (@0 A : Set) → A) → Set
