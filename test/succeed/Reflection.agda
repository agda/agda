{-# OPTIONS --universe-polymorphism #-}
module Reflection where

open import Common.Prelude
open import Common.Reflect

data _≡_ {A : Set}(x : A) : A → Set where
  refl : x ≡ x

{-# BUILTIN EQUALITY _≡_ #-}
{-# BUILTIN REFL refl #-}

data Id {A : Set}(x : A) : (B : Set) → B → Set where
  course : Id x A x

primitive primTrustMe : {A : Set}{x y : A} → x ≡ y

open import Common.Level

argᵛʳ : ∀{A} → A → Arg A
argᵛʳ = arg visible relevant

argʰʳ : ∀{A} → A → Arg A
argʰʳ = arg hidden relevant

el₀ : Term → Type
el₀ = el (lit 0)

el₁ : Term → Type
el₁ = el (lit 1)

unCheck : Term → Term
unCheck (def x (_ ∷ _ ∷ arg _ _ t ∷ [])) = t
unCheck t = unknown

mutual
  data Check {a}{A : Set a}(x : A) : Set where
    _is_of_ : (t t′ : Term) →
              Id (primTrustMe {x = unCheck t} {t′}
                 )
                 (t′ ≡ t′) refl → Check x

  `Check : QName
  `Check = quote Check

test₁ : Check ({A : Set} → A → A)
test₁ = quoteGoal t in
        t is pi (argʰʳ (el₁ (sort (lit 0)))) (el₀ (pi (argᵛʳ (el₀ (var 0 []))) (el₀ (var 1 []))))
        of course

test₂ : (X : Set) → Check (λ (x : X) → x)
test₂ X = quoteGoal t in
          t is lam visible (var 0 []) of course

infixr 40 _`∷_

_`∷_ : Term → Term → Term
x `∷ xs = con (quote _∷_) (argᵛʳ x ∷ argᵛʳ xs ∷ [])
`[]     = con (quote []) []
`true   = con (quote true) []
`false  = con (quote false) []

test₃ : Check (true ∷ false ∷ [])
test₃ = quoteGoal t in
        t is `true `∷ `false `∷ `[] of course

`List : Term → Term
`List A = def (quote List) (argᵛʳ A ∷ [])
`Nat    = def (quote Nat) []

test₄ : Check (List Nat)
test₄ = quoteGoal t in
        t is `List `Nat of course
