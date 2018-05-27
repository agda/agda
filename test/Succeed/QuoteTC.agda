-- Test unquoteTC and quoteTC primitives.
module _ where

open import Common.Prelude hiding (_>>=_)
open import Common.Reflection
open import Common.Equality
open import Common.Product

sum : List Nat → Nat
sum [] = 0
sum (x ∷ xs) = x + sum xs

pattern `Bool = def (quote Bool) []
pattern `true = con (quote true) []
pattern `false = con (quote false) []

infix 2 case_of_
case_of_ : ∀ {a b} {A : Set a} {B : Set b} → A → (A → B) → B
case x of f = f x

macro
  ` : Term → Tactic
  ` v hole = bindTC (quoteTC v) λ e → unify hole e

  ~ : Term → Tactic
  ~ e hole = bindTC (unquoteTC e) λ v → unify hole v

  msum : Term → Tactic
  msum e hole = bindTC (unquoteTC e) λ xs → unify hole (lit (nat (sum xs)))

test₁ : Term
test₁ = ` (1 ∷ 2 ∷ 3 ∷ [])

test₂ : ~ test₁ ≡ (1 ∷ 2 ∷ 3 ∷ [])
test₂ = refl

test₃ : msum (1 ∷ 2 ∷ 3 ∷ []) ≡ 6
test₃ = refl

macro
  simp : Term → Tactic
  simp (def f (vArg x ∷ [])) hole =
    checkType (def f []) (pi (vArg `Bool) (abs "_" `Bool)) >>= λ _ →
    unquoteTC (def f (vArg `true  ∷ [])) >>= λ (t : Bool) →
    unquoteTC (def f (vArg `false ∷ [])) >>= λ (f : Bool) →
    unify hole (case (t , f) of λ
    { (true , true)   → `true
    ; (false , false) → `false
    ; (true , false)  → x
    ; (false , true)  → def (quote not) (vArg x ∷ [])
    })
  simp v _ = typeError (strErr "Can't simplify" ∷ termErr v ∷ [])

f₁ f₂ f₃ f₄ : Bool → Bool
f₁ false = false
f₁ true  = false

f₂ false = false
f₂ true  = true

f₃ false = true
f₃ true  = false

f₄ false = true
f₄ true  = true

test-f₁ : ∀ b → simp (f₁ b) ≡ false
test-f₁ b = refl

test-f₂ : ∀ b → simp (f₂ b) ≡ b
test-f₂ b = refl

test-f₃ : ∀ b → simp (f₃ b) ≡ not b
test-f₃ b = refl

test-f₄ : ∀ b → simp (f₄ b) ≡ true
test-f₄ b = refl
