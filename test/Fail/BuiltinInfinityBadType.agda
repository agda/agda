
open import Agda.Primitive

postulate
  ∞  : ∀ {a} (A : Set a) → Set (lsuc a)

{-# BUILTIN INFINITY ∞  #-}
