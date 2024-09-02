open import Agda.Builtin.List
open import Agda.Builtin.Unit
open import Agda.Builtin.Nat
open import Agda.Builtin.Reflection
  renaming (bindTC to _>>=_; returnTC to return)

pattern vArg t = arg (arg-info visible (modality relevant quantity-ω)) t

const : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} → A → B → A
const a b = a

macro
  test : Term → TC ⊤
  test _ = do
    _ ← extendContext "a" (vArg (quoteTerm Nat)) do
      x ← unquoteTC {A = Nat} (var 0 [])
      return {A = Nat} (const 0 x)
    return tt

_ : ⊤
_ = test
