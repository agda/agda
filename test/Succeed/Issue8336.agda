{-# OPTIONS --double-check #-}     -- on by default in the testsuite
{-# OPTIONS --projection-like #-}  -- on by default

module Issue8336 where

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

concat : {A : Set} → {x y z : A} → x ≡ y → y ≡ z → x ≡ z
concat refl refl = refl

data Σ (A : Set) (B : A → Set) : Set where
  _,_ : (x : A) → B x → Σ A B

-- proj₁ and proj₂ are projection-_like_ functions on a _data_ type.

proj₁ : {A : Set} → {B : A → Set} → Σ A B → A
proj₁ (x , y) = x

proj₂ : {A : Set} → {B : A → Set} → (z : Σ A B) → B (proj₁ z)
proj₂ (x , y) = y

_×_ : Set → Set → Set
A × B = Σ A (λ _ → B)

S : Set → Set
S A = Σ (A → A) (λ f → (x : A) → f x ≡ x)

p : {X : Set} → (u : X → X) → ((x : X) → u x ≡ x) → (S X → S X) × (S X → S X)
p u hu = (λ z → (λ x → u (proj₁ z x)) , (λ x → concat (hu (proj₁ z x)) (proj₂ z x))) , (λ z → z)

goal : {X : Set} → (u : X → X) → (hu : (x : X) → u x ≡ x) → (s : S X) → (x : X)
  → proj₂ (proj₁ (p u hu) s) x ≡ proj₂ (proj₁ (p u hu) s) x
goal u hu s x = concat refl refl
