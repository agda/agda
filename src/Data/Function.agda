------------------------------------------------------------------------
-- Simple combinators working solely on and with functions
------------------------------------------------------------------------

module Data.Function where

infixr 9 _∘_ _∘′_ _∘₀_ _∘₁_
infixl 1 _on_ _on₁_
infixl 1 _⟨_⟩_ _⟨_⟩₁_
infixr 0 _-[_]₁-_ _-[_]-_ _$_
infix  0 _∶_ _∶₁_

------------------------------------------------------------------------
-- Types

-- Unary functions on a given set.

Fun₁ : Set → Set
Fun₁ a = a → a

-- Binary functions on a given set.

Fun₂ : Set → Set
Fun₂ a = a → a → a

------------------------------------------------------------------------
-- Functions

_∘_ : {A : Set} {B : A → Set} {C : {x : A} → B x → Set} →
      (∀ {x} (y : B x) → C y) → (g : (x : A) → B x) →
      ((x : A) → C (g x))
f ∘ g = λ x → f (g x)

_∘′_ : {A B C : Set} → (B → C) → (A → B) → (A → C)
f ∘′ g = _∘_ f g

_∘₀_ : {A : Set} {B : A → Set} {C : {x : A} → B x → Set₁} →
       (∀ {x} (y : B x) → C y) → (g : (x : A) → B x) →
       ((x : A) → C (g x))
f ∘₀ g = λ x → f (g x)

_∘₁_ : {A : Set₁} {B : A → Set₁} {C : {x : A} → B x → Set₁} →
       (∀ {x} (y : B x) → C y) → (g : (x : A) → B x) →
       ((x : A) → C (g x))
f ∘₁ g = λ x → f (g x)

id : {a : Set} → a → a
id x = x

id₁ : {a : Set₁} → a → a
id₁ x = x

const : {a b : Set} → a → b → a
const x = λ _ → x

const₁ : {a : Set₁} {b : Set} → a → b → a
const₁ x = λ _ → x

flip : {A B : Set} {C : A → B → Set} →
       ((x : A) (y : B) → C x y) → ((y : B) (x : A) → C x y)
flip f = λ x y → f y x

flip₁ : {A B : Set} {C : A → B → Set₁} →
        ((x : A) (y : B) → C x y) → ((y : B) (x : A) → C x y)
flip₁ f = λ x y → f y x

-- Note that _$_ is right associative, like in Haskell. If you want a
-- left associative infix application operator, use
-- Category.Functor._<$>_, available from
-- Category.Monad.Identity.IdentityMonad.

_$_ : {a : Set} {b : a → Set} → ((x : a) → b x) → ((x : a) → b x)
f $ x = f x

_⟨_⟩_ : {a b c : Set} → a → (a → b → c) → b → c
x ⟨ f ⟩ y = f x y

_⟨_⟩₁_ : {a b : Set} → a → (a → b → Set) → b → Set
x ⟨ f ⟩₁ y = f x y

_on_ : {a b c : Set} → (b → b → c) → (a → b) → (a → a → c)
_*_ on f = λ x y → f x * f y

_on₁_ : {a b : Set} {c : Set₁} → (b → b → c) → (a → b) → (a → a → c)
_*_ on₁ f = λ x y → f x * f y

_-[_]-_ : {a b c d e : Set} →
          (a → b → c) → (c → d → e) → (a → b → d) → (a → b → e)
f -[ _*_ ]- g = λ x y → f x y * g x y

_-[_]₁-_ : {a b : Set} →
           (a → b → Set) → (Set → Set → Set) → (a → b → Set) →
           (a → b → Set)
f -[ _*_ ]₁- g = λ x y → f x y * g x y

-- In Agda you cannot annotate every subexpression with a type
-- signature. This function can be used instead.
--
-- You should think of the colon as being mirrored around its vertical
-- axis; the type comes first.

_∶_ : (A : Set) → A → A
_ ∶ x = x

_∶₁_ : (A : Set₁) → A → A
_ ∶₁ x = x
