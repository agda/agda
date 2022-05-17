
-- Tests for withNormalisation

module _ where

open import Agda.Builtin.Reflection
open import Agda.Builtin.Nat
open import Agda.Builtin.Equality
open import Agda.Builtin.Bool
open import Agda.Builtin.Unit
open import Agda.Builtin.List

infixl 4 _>>=_
_>>=_ = bindTC

F : Bool → Set
F false = Nat
F true  = Bool

data D (b : Bool) : Set where

_&&_ : Bool → Bool → Bool
true  && x = x
false && _ = false

postulate
  reflected : ∀ {a} {A : Set a} → Term → A

pattern vArg x = arg (arg-info visible (modality relevant quantity-ω)) x

useReflected : Term → Term → TC ⊤
useReflected hole goal =
  quoteTC goal >>= λ `goal →
  unify hole (def (quote reflected) (vArg `goal ∷ []))

macro
  error : Term → TC ⊤
  error hole =
    inferType hole >>= λ goal → typeError (termErr goal ∷ [])

  reflect : Term → TC ⊤
  reflect hole = inferType hole >>= useReflected hole

  reflectN : Term → TC ⊤
  reflectN hole = withNormalisation true (inferType hole) >>= useReflected hole

test₁ : D (true && false)
test₁ = reflect

test₂ : D (true && false)
test₂ = reflectN

pattern `D x = def (quote D) (vArg x ∷ [])
pattern `true = con (quote true) []
pattern `false = con (quote false) []
pattern _`&&_ x y = def (quote _&&_) (vArg x ∷ vArg y ∷ [])

check₁ : test₁ ≡ reflected (`D (`true `&& `false))
check₁ = refl

check₂ : test₂ ≡ reflected (`D `false)
check₂ = refl
