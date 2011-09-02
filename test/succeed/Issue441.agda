{-# OPTIONS --universe-polymorphism #-}

module Issue441 where

open import Common.Level

postulate
  C : ∀ ℓ → Set ℓ → Set ℓ
  I : ∀ a b (A : Set a) (B : Set b) → (A → B) → B → Set (a ⊔ b)
  E : ∀ a b (A : Set a) → (A → Set b) → Set (a ⊔ b)
  c : ∀ a (A : Set a) → ((B : A → Set a) → E a a A B) → C a A

foo : (∀ a b (A : Set a) (B : A → Set b) → E a b A B) →
      ∀ a b (A : Set a) (B : Set b) (f : A → B) x →
      C (a ⊔ b) (I a b A B f x)
foo e a b A B f x = c _ _ (λ B′ → e _ _ _ _)

infix 4 _≡_

data _≡_ {a} {A : Set a} : A → A → Set a where
  refl : ∀ x → x ≡ x

elim : ∀ {a p} {A : Set a} (P : {x y : A} → x ≡ y → Set p) →
       (∀ x → P (refl x)) →
       ∀ {x y} (x≡y : x ≡ y) → P x≡y
elim P r (refl x) = r _

cong : ∀ {a b} {A : Set a} {B : Set b}
       (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
cong f (refl x) = refl (f x)

bar : ∀ {a} {A : Set a} {x y : A}
      (x≡y : x ≡ y) (f : x ≡ y → x ≡ y) →
      f x≡y ≡ f x≡y
bar = elim (λ {x} {y} x≡y → (f : x ≡ y → x ≡ y) → f x≡y ≡ f x≡y)
           (λ x f → cong {a = _} {b = _} f (refl (refl x)))

