-- Check that errors from tactics are displayed properly.
module _ where

open import Common.Prelude hiding (_>>=_)
open import Common.Equality
open import Common.Reflection

failTactic : Term → TC ⊤
failTactic hole =
  inferType hole >>= λ goal →
  typeError (strErr "Surprisingly the " ∷ nameErr (quote failTactic) ∷
             strErr " failed to prove " ∷ termErr goal ∷ [])

macro
  proveIt = failTactic

postulate
  ComplexityClass : Set
  P NP : ComplexityClass

thm : P ≡ NP → ⊥
thm = proveIt
