------------------------------------------------------------------------
-- Simple combinators working solely on and with functions
------------------------------------------------------------------------

{-# OPTIONS --universe-polymorphism #-}

module Function where

open import Level

infixr 9 _∘_ _∘′_
infixl 1 _on_
infixl 1 _⟨_⟩_
infixr 0 _-[_]-_ _$_
infix  0 type-signature

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

flip : ∀ {a b c} {A : Set a} {B : Set b} {C : A → B → Set c} →
       ((x : A) (y : B) → C x y) → ((y : B) (x : A) → C x y)
flip f = λ x y → f y x

-- Note that _$_ is right associative, like in Haskell. If you want a
-- left associative infix application operator, use
-- Category.Functor._<$>_, available from
-- Category.Monad.Identity.IdentityMonad.

_$_ : ∀ {a b} {A : Set a} {B : A → Set b} →
      ((x : A) → B x) → ((x : A) → B x)
f $ x = f x

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

type-signature : ∀ {a} (A : Set a) → A → A
type-signature A x = x

syntax type-signature A x = x ∶ A
