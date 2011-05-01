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

primitive
  primTrustMe : {A : Set}{x y : A} → x ≡ y
  primQNameType : QName → Type

open import Common.Level

unEl : Type → Term
unEl (el _ t) = t

argᵛʳ : ∀{A} → A → Arg A
argᵛʳ = arg visible relevant

argʰʳ : ∀{A} → A → Arg A
argʰʳ = arg hidden relevant

el₀ : Term → Type
el₀ = el (lit 0)

el₁ : Term → Type
el₁ = el (lit 1)

set₀ : Type
set₀ = el₁ (sort (lit 0))

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
        t is pi (argʰʳ set₀) (el₀ (pi (argᵛʳ (el₀ (var 0 []))) (el₀ (var 1 []))))
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

`Term : Term
`Term = def (quote Term) []
`Type : Term
`Type = def (quote Type) []
`Sort : Term
`Sort = def (quote Sort) []

test₄ : Check (List Nat)
test₄ = quoteGoal t in
        t is `List `Nat of course

test₅ : primQNameType (quote Term) ≡ set₀
test₅ = refl

-- TODO => test₆ : primQNameType (quote set₀) ≡ el unknown `Type ≢ el₀ `Type
test₆ : unEl (primQNameType (quote set₀)) ≡ `Type
test₆ = refl

test₇ : primQNameType (quote Sort.lit) ≡ el₀ (pi (argᵛʳ (el₀ `Nat)) (el₀ `Sort))
test₇ = refl
