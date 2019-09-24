{-# OPTIONS --universe-polymorphism #-}
module Reflection where

open import Common.Prelude hiding (Unit; module Unit) renaming (Nat to ℕ; module Nat to ℕ)
open import Common.Reflection
open import Common.Equality
open import Agda.Builtin.TrustMe

data Id {A : Set}(x : A) : (B : Set) → B → Set where
  course : Id x A x

open import Common.Level

set₀ : Type
set₀ = sort (lit 0)

unCheck : Term → Term
unCheck (def x (_ ∷ _ ∷ arg _ t ∷ [])) = t
unCheck t = unknown

infix 1 _is_of_
data Check {a}{A : Set a}(x : A) : Set where
  _is_of_ : (t t′ : Term) →
            Id (primTrustMe {x = unCheck t} {t′})
               (t′ ≡ t′) refl → Check x

`Check : QName
`Check = quote Check

infixr 5 _`∷_

pattern _`∷_ x xs = con (quote _∷_) (hArg unknown ∷ hArg unknown ∷ vArg x ∷ vArg xs ∷ [])
pattern `[]    = con (quote []) (hArg unknown ∷ hArg unknown ∷ [])
pattern `true  = con (quote true) []
pattern `false = con (quote false) []

`List : Term → Term
`List A = def (quote List) (hArg (def (quote lzero) []) ∷ vArg A ∷ [])
`ℕ      = def (quote ℕ) []

`Term : Term
`Term = def (quote Term) []
`Type : Term
`Type = def (quote Type) []
`Sort : Term
`Sort = def (quote Sort) []

postulate
  a : ℕ

record R : Set₁ where
  field
    A : Set

macro

  RA : Term → TC _
  RA goal = bindTC (getDefinition (quote R)) λ where
    (recordDef _ (vArg A ∷ [])) → unify goal (def A [])
    _                           → typeError (strErr "Impossible" ∷ [])

test₁₅ : RA ≡ R.A
test₁₅ = refl
