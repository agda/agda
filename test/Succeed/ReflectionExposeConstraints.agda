module ReflectionExposeConstraints where

open import Agda.Builtin.Reflection
open import Agda.Builtin.List
open import Agda.Builtin.Nat
open import Agda.Builtin.Unit
open import Agda.Builtin.Equality

_>>=_ : ∀ {a b} {A : Set a} {B : Set b} → TC A → (A → TC B) → TC B
_>>=_ = bindTC

_ifMeta_ : {A : Set} → Term → (Meta → TC A) → TC A
meta x x₁ ifMeta f = f x
_ ifMeta _ = typeError (strErr "Error1" ∷ [])

infixr 0 case_of_
case_of_ : ∀ {a b} {A : Set a} {B : Set b} → A → (A → B) → B
case x of f = f x


foo : Constraint → TC Term
foo (valueCmp cmpEq y t1 (def f args)) = returnTC (def f [])
foo _ = typeError (strErr "Error2" ∷ [])

q : Nat → Nat
q zero = 4
q (suc x) = 4

macro
  mfun : Term → TC ⊤
  mfun hole
     = delayMacro >>= (λ _ →
         hole ifMeta (λ x → do
                              c ← getConstraintsMentioning (x ∷ [])
                              case c of
                                λ {[] → typeError (strErr "Error3" ∷ [])
                                  ; (c ∷ cs) → do
                                                 g ← foo c
                                                 unify hole g }
                              ))
postulate
  g : (Q : Nat → Nat) → ∀ k → Q k ≡ 4

f : ∀ k → q k ≡ 4
f k = g mfun k
