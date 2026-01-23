{-# OPTIONS --erasure #-}

open import Agda.Primitive

postulate
  ∞  : ∀ {@0 a} (A : Set a) → Set (lsuc a)

{-# BUILTIN INFINITY ∞  #-}
