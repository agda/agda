module ReflectionLiterals where

open import Agda.Primitive
open import Agda.Builtin.Unit
open import Agda.Builtin.Nat
open import Agda.Builtin.List
open import Agda.Builtin.Equality
open import Agda.Builtin.Reflection renaming (bindTC to infixl 4 _>>=_)

variable
  ℓ : Level
  A : Set ℓ

_>>_ : {A B : Set} → TC A → TC B → TC B
m >> m' = m >>= λ _ → m'

inception : Nat → Term → TC Term
inception zero    t = returnTC t
inception (suc n) t = quoteTC t >>= inception n

unception : Nat → Term → TC Term
unception zero    t = returnTC t
unception (suc n) t = unquoteTC t >>= unception n

quoteN : {A : Set} → Nat → A → TC Term
quoteN n x = quoteTC x >>= inception n >>= unception n

macro
  incept : {A : Set} → Nat → A → Term → TC ⊤
  incept n x hole = quoteN n x >>= unify hole

-- This blows up at level 4 without reflection literals.
test : List Nat
test = incept 500 (1 ∷ 2 ∷ [])

check : test ≡ 1 ∷ 2 ∷ []
check = refl
