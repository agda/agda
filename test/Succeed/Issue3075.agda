{-# OPTIONS --no-auto-inline #-}

open import Agda.Builtin.Reflection renaming (bindTC to _>>=_)
open import Agda.Builtin.Nat
open import Agda.Builtin.Unit
open import Agda.Builtin.List
open import Agda.Builtin.Equality

_>>_ : {A B : Set} → TC A → TC B → TC B
m >> m' = m >>= λ _ → m'

-- Normally auto-inlined
id : {A : Set} → A → A
id x = x

id-inline : {A : Set} → A → A
id-inline x = x
{-# INLINE id-inline #-}

f₁ : Nat → Nat
f₁ n = id n

f₂ : Nat → Nat
f₂ n = id-inline n

macro
  rhs : Name → Term → TC ⊤
  rhs f hole = do
    function (clause _ _ rhs ∷ _) ← getDefinition f
      where _ → typeError (strErr "fail" ∷ [])
    `rhs ← quoteTC rhs
    unify hole `rhs

pattern vArg x = arg (arg-info visible relevant) x
pattern hArg x = arg (arg-info hidden relevant) x

-- Should not be inlined
check₁ : rhs f₁ ≡ def (quote id) (hArg (def (quote Nat) []) ∷ vArg (var 0 []) ∷ [])
check₁ = refl

-- Should be inlined
check₂ : rhs f₂ ≡ var 0 []
check₂ = refl
