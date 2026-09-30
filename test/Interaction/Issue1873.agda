
module _ where

id : {A : Set} → A → A
id x = x

const : {A : Set₁} {B : Set} → A → (B → A)
const x = λ _ → x

{-# DISPLAY const x y = x #-}

infixr 4 _,_
infixr 2 _×_

record Σ (A : Set) (B : A → Set) : Set where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B proj₁

open Σ public

_×_ : (A B : Set) → Set
A × B = Σ A (const B)

Σ-map : ∀ {A B : Set} {P : A → Set} {Q : B → Set} →
        (f : A → B) → (∀ {x} → P x → Q (f x)) →
        Σ A P → Σ B Q
Σ-map f g = λ p → (f (proj₁ p) , g (proj₂ p))

foo : {A B : Set} → A × B → A × B
foo = Σ-map id {!!}
