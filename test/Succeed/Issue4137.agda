{-# OPTIONS --erasure #-}

open import Agda.Builtin.List

foldr : {A B : Set} → (A → B → B) → B → List A → B
foldr _⊕_ ε []       = ε
foldr _⊕_ ε (x ∷ xs) = x ⊕ foldr _⊕_ ε xs

infixr 5 _++_

_++_ : {A : Set} → List A → List A → List A
xs ++ ys = foldr _∷_ ys xs

record R (F : Set → Set) : Set₁ where
  field
    f : {A : Set} → A → F A → F A

open R ⦃ … ⦄ public

postulate
  D    : {A : Set} → List A → Set
  easy : {A : Set} {@0 xs : List A} → D xs

record Q (A : Set) : Set where
  field
    @0 index : List A
    d        : D index

g : {A : Set} → A → Q A → Q A
g x q .Q.index = q .Q.index ++ x ∷ []
g x q .Q.d     = easy

record _×_ (A B : Set) : Set where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B

data Maybe (A : Set) : Set where
  nothing : Maybe A
  just    : A → Maybe A

postulate
  m₁ : {A : Set} {B : Maybe A → Set} →
       ((x : A) → B (just x)) → (x : Maybe A) → B x

m₂ : {A B : Set} → (A → Maybe B) → Maybe A → Maybe B
m₂ f x = m₁ f x

postulate
  P : {A : Set} → A → Set
  p : {A : Set} (x : A) → P x
  A : Set
  x : Maybe (A × Q A)

instance
  _ : R Q
  _ = record { f = g }

_ : P (m₂ (λ { (x , q) → just (f x q) }) x)
_ = p (m₁ (λ { (x , q) → just (f x q) }) x)
