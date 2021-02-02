
module _ where

open import Agda.Builtin.Reflection renaming (bindTC to _>>=_)
open import Agda.Builtin.Equality
open import Agda.Builtin.String

macro
  m : Name → Term → TC _
  m f hole = do
     ty ← getType f
     ty ← normalise ty
     quoteTC ty >>= unify hole

open import Agda.Builtin.Nat

import Agda.Builtin.Nat as Nat₁ renaming (Nat to Hombre)
import Agda.Builtin.Nat as Nat₂ renaming (Nat to ℕumber)
import Agda.Builtin.Nat as Nat₃ renaming (Nat to n)
import Agda.Builtin.Nat as Nat₄ renaming (Nat to N)

infix 0 _∋_
_∋_ : (A : Set) → A → A
A ∋ x = x

binderName : Term → String
binderName (pi _ (abs x _)) = x
binderName _                = "(no binder)"

f₁ : Nat₁.Hombre → Nat
f₁ x = x

f₂ : Nat₂.ℕumber → Nat
f₂ x = x

f₃ : Nat₃.n → Nat
f₃ x = x

f₄ : Nat₄.N → Nat
f₄ x = x

_ = binderName (m f₁) ≡ "h" ∋ refl
_ = binderName (m f₂) ≡ "z" ∋ refl  -- Can't toLower ℕ
_ = binderName (m f₃) ≡ "z" ∋ refl  -- Single lower case type name, don't pick same name for binder
_ = binderName (m f₄) ≡ "n" ∋ refl
