
open import Common.Prelude hiding (pred)
open import Common.Reflection
open import Common.Equality

un-function : Definition → FunDef
un-function (funDef cs) = funDef unknown cs
un-function _           = funDef unknown []

data Is-suc : Nat → Set where
  is-suc : ∀ n → Is-suc (suc n)

pred : (n : Nat) → Is-suc n → Nat
pred ._ (is-suc n) = n

pred-def : FunDef
pred-def =
  funDef (quoteTerm ((n : Nat) → Is-suc n → Nat))
         (clause (vArg dot ∷ vArg (con (quote is-suc) (vArg (var "n") ∷ [])) ∷ [])
                 (var 0 []) ∷ [])

data Is-zero : Nat → Set where
  is-zero : Is-zero zero

f : (n : Nat) → Is-zero n → Nat
f ._ is-zero = zero

f-def : FunDef
f-def =
  funDef (quoteTerm ((n : Nat) → Is-zero n → Nat))
         (clause (vArg dot ∷ vArg (con (quote is-zero) []) ∷ [])
                 (con (quote zero) []) ∷ [])

unquoteDecl pred' = define (vArg pred') pred-def
unquoteDecl f'    = define (vArg f')    f-def

check-pred : pred' 4 (is-suc _) ≡ 3
check-pred = refl

check-f : f' 0 is-zero ≡ 0
check-f = refl
