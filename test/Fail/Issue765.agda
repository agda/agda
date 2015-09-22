{-# OPTIONS --without-K #-}

module Issue765 where

infixr 1 _⊎_
infixr 4 _,_
infix 4 _≡_

data ⊥ : Set where

⊥-elim : {A : Set} → ⊥ → A
⊥-elim ()

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

data _⊎_ (A : Set) (B : Set) : Set where
  inj₁ : (x : A) → A ⊎ B
  inj₂ : (y : B) → A ⊎ B

[_,_]₁ : ∀ {A : Set} {B : Set} {C : A ⊎ B → Set₁} →
        ((x : A) → C (inj₁ x)) → ((x : B) → C (inj₂ x)) →
        ((x : A ⊎ B) → C x)
[ f , g ]₁ (inj₁ x) = f x
[ f , g ]₁ (inj₂ y) = g y


record Σ (A : Set) (B : A → Set) : Set where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B proj₁

open Σ public

infix 5 _◃_
infixr 1 _⊎C_

record Container : Set₁ where
  constructor _◃_
  field
    Shape     : Set
    Position  : Shape → Set

open Container public

constC : Set → Container
constC X = X ◃ λ _ → ⊥

_⊎C_ : Container → Container → Container
S ◃ P ⊎C S′ ◃ P′ = (S ⊎ S′) ◃ [ P , P′ ]₁

data μ (C : Container) : Set where
  sup : (s : Shape C) (k : Position C s → μ C) → μ C

_⋆_ : Container → Set → Set
C ⋆ X = μ (constC X ⊎C C)

to : ∀ {C X} → C ⋆ X → C ⋆ (C ⋆ X)
to m = sup (inj₁ m) ⊥-elim

injective : ∀ {C X}{m n : C ⋆ X} → to m ≡ to n → m ≡ n
injective refl = refl
