module Issue6959a where

open import Agda.Builtin.Equality
open import Agda.Builtin.List
open import Agda.Builtin.Reflection

open Agda.Primitive

data D : Set where
  c : D

opaque
  unquoteDecl c′ =
     bindTC
       (declareDef
          (arg (arg-info visible (modality relevant quantity-ω)) c′)
          (def (quote D) [])) λ _ →
     defineFun c′ (clause [] [] (con (quote c) []) ∷ [])

_ : c ≡ c′
_ = refl
