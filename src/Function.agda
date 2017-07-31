------------------------------------------------------------------------
-- The Agda standard library
--
-- Simple combinators working solely on and with functions
------------------------------------------------------------------------

module Function where

open import Level
open import Strict

infixr 9 _∘_ _∘′_
infixl 8 _ˢ_
infixl 1 _on_
infixl 1 _⟨_⟩_
infixr 0 _-[_]-_ _$_ _$′_ _$!_ _$!′_
infixl 0 _∋_

------------------------------------------------------------------------
-- Types

-- Unary functions on a given set.

Fun₁ : ∀ {i} → Set i → Set i
Fun₁ A = A → A

-- Binary functions on a given set.

Fun₂ : ∀ {i} → Set i → Set i
Fun₂ A = A → A → A

------------------------------------------------------------------------
-- Functions

_∘_ : ∀ {a b c}
        {A : Set a} {B : A → Set b} {C : {x : A} → B x → Set c} →
        (∀ {x} (y : B x) → C y) → (g : (x : A) → B x) →
        ((x : A) → C (g x))
f ∘ g = λ x → f (g x)

_∘′_ : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c} →
         (B → C) → (A → B) → (A → C)
f ∘′ g = _∘_ f g

id : ∀ {a} {A : Set a} → A → A
id x = x

const : ∀ {a b} {A : Set a} {B : Set b} → A → B → A
const x = λ _ → x

-- The S combinator. (Written infix as in Conor McBride's paper
-- "Outrageous but Meaningful Coincidences: Dependent type-safe syntax
-- and evaluation".)

_ˢ_ : ∀ {a b c}
        {A : Set a} {B : A → Set b} {C : (x : A) → B x → Set c} →
      ((x : A) (y : B x) → C x y) →
      (g : (x : A) → B x) →
      ((x : A) → C x (g x))
f ˢ g = λ x → f x (g x)

flip : ∀ {a b c} {A : Set a} {B : Set b} {C : A → B → Set c} →
       ((x : A) (y : B) → C x y) → ((y : B) (x : A) → C x y)
flip f = λ y x → f x y

-- Note that _$_ is right associative, like in Haskell. If you want a
-- left associative infix application operator, use
-- Category.Functor._<$>_, available from
-- Category.Monad.Identity.IdentityMonad.

_$_ : ∀ {a b} {A : Set a} {B : A → Set b} →
      ((x : A) → B x) → ((x : A) → B x)
f $ x = f x

_$′_ : ∀ {a b} {A : Set a} {B : Set b} →
       (A → B) → (A → B)
_$′_ = _$_

-- Strict (call-by-value) application

_$!_ : ∀ {a b} {A : Set a} {B : A → Set b} →
       ((x : A) → B x) → ((x : A) → B x)
_$!_ = flip force

_$!′_ : ∀ {a b} {A : Set a} {B : Set b} →
        (A → B) → (A → B)
_$!′_ = _$!_


_⟨_⟩_ : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c} →
        A → (A → B → C) → B → C
x ⟨ f ⟩ y = f x y

_on_ : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c} →
       (B → B → C) → (A → B) → (A → A → C)
_*_ on f = λ x y → f x * f y

_-[_]-_ : ∀ {a b c d e} {A : Set a} {B : Set b} {C : Set c}
            {D : Set d} {E : Set e} →
          (A → B → C) → (C → D → E) → (A → B → D) → (A → B → E)
f -[ _*_ ]- g = λ x y → f x y * g x y

-- In Agda you cannot annotate every subexpression with a type
-- signature. This function can be used instead.

_∋_ : ∀ {a} (A : Set a) → A → A
A ∋ x = x

-- Case expressions (to be used with pattern-matching lambdas, see
-- README.Case).

infix 0 case_return_of_ case_of_

case_return_of_ :
  ∀ {a b} {A : Set a}
  (x : A) (B : A → Set b) → ((x : A) → B x) → B x
case x return B of f = f x

case_of_ : ∀ {a b} {A : Set a} {B : Set b} → A → (A → B) → B
case x of f = case x return _ of f
