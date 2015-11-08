
open import Common.Prelude hiding (pred)
open import Common.Reflection
open import Common.Equality

un-function : Definition → FunDef
un-function (funDef x) = x
un-function _          = funDef (el unknown unknown) []

data Is-suc : Nat → Set where
  is-suc : ∀ n → Is-suc (suc n)

pred : (n : Nat) → Is-suc n → Nat
pred ._ (is-suc n) = n

pred-def = un-function (primQNameDefinition (quote pred))

data Is-zero : Nat → Set where
  is-zero : Is-zero zero

f : (n : Nat) → Is-zero n → Nat
f ._ is-zero = zero

f-def = un-function (primQNameDefinition (quote f))

unquoteDecl pred' = pred-def
unquoteDecl f'    = f-def

check-pred : pred' 4 (is-suc _) ≡ 3
check-pred = refl

check-f : f' 0 is-zero ≡ 0
check-f = refl
