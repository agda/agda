{-# OPTIONS --universe-polymorphism #-}
module Reflection where

open import Common.Prelude hiding (Unit; module Unit) renaming (Nat to ℕ; module Nat to ℕ)
open import Common.Reflection

data _≡_ {a}{A : Set a}(x : A) : A → Set a where
  refl : x ≡ x

{-# BUILTIN EQUALITY _≡_ #-}
{-# BUILTIN REFL refl #-}

data Id {A : Set}(x : A) : (B : Set) → B → Set where
  course : Id x A x

primitive
  primTrustMe : ∀{a}{A : Set a}{x y : A} → x ≡ y

open import Common.Level

set₀ : Type
set₀ = sort (lit 0)

unCheck : Term → Term
unCheck (def x (_ ∷ _ ∷ arg _ t ∷ [])) = t
unCheck t = unknown

data Check {a}{A : Set a}(x : A) : Set where
  _is_of_ : (t t′ : Term) →
            Id (primTrustMe {x = unCheck t} {t′})
               (t′ ≡ t′) refl → Check x

`Check : QName
`Check = quote Check

test₁ : Check ({A : Set} → A → A)
test₁ = quoteGoal t in
        t is pi (hArg set₀) (abs "A" (pi (vArg (var 0 [])) (abs "_" (var 1 []))))
        of course

test₂ : (X : Set) → Check (λ (x : X) → x)
test₂ X = quoteGoal t in
          t is lam visible (abs "x" (var 0 [])) of course

infixr 40 _`∷_

pattern _`∷_ x xs = con (quote _∷_) (hArg unknown ∷ vArg x ∷ vArg xs ∷ [])
pattern `[]    = con (quote []) (hArg unknown ∷ [])
pattern `true  = con (quote true) []
pattern `false = con (quote false) []

test₃ : Check (true ∷ false ∷ [])
test₃ = quoteGoal t in
        t is `true `∷ `false `∷ `[] of course

`List : Term → Term
`List A = def (quote List) (vArg A ∷ [])
`ℕ      = def (quote ℕ) []

`Term : Term
`Term = def (quote Term) []
`Type : Term
`Type = def (quote Type) []
`Sort : Term
`Sort = def (quote Sort) []

test₄ : Check (List ℕ)
test₄ = quoteGoal t in
        t is `List `ℕ of course

postulate
  a : ℕ

test₁₄ : Check 1
test₁₄ = quoteGoal t in t is lit (nat 1) of course
