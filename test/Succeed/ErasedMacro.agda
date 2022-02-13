open import Agda.Builtin.Unit
open import Agda.Builtin.List
open import Agda.Builtin.Nat
open import Agda.Builtin.Equality
open import Agda.Builtin.Reflection
open import Agda.Builtin.Sigma

macro
  @0 trivial : Term → TC ⊤
  trivial = unify (con (quote refl) [])

test : 42 ≡ 42
test = trivial

@0 m : Name → TC ⊤
m F = defineFun F
  (clause
     (( "A"
      , arg (arg-info visible (modality relevant quantity-0))
          (agda-sort (lit 0))) ∷
      [])
     (arg (arg-info visible (modality relevant quantity-0)) (var 0) ∷
      [])
     (var 0 []) ∷
   [])

F : Set → Set
unquoteDef F = m F
