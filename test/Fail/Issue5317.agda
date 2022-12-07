{-# OPTIONS --erasure #-}

open import Agda.Builtin.List
open import Agda.Builtin.Reflection
open import Agda.Builtin.Unit

macro

  m : Term → TC ⊤
  m _ =
    bindTC (quoteTC (Set → @0 Set → Set)) λ t →
    typeError (termErr t ∷ [])

_ : Set
_ = m
