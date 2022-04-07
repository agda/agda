{-# OPTIONS --cubical-compatible --rewriting --local-confluence-check #-}

open import Agda.Primitive using (Level; _⊔_; Setω; lzero; lsuc)

infix 4 _≡_

data _≡_ {ℓ : Level} {A : Set ℓ} (a : A) : A → Set ℓ where
  refl : a ≡ a

{-# BUILTIN REWRITE _≡_ #-}

run : ∀ {ℓ} {A B : Set ℓ} → A ≡ B → A → B
run refl x = x

ap : ∀ {a b} {A : Set a} {B : Set b} (f : A → B) {a₁ a₂} → a₁ ≡ a₂ → f a₁ ≡ f a₂
ap f refl = refl

transport1 : ∀ {a b} {A : Set a} (B : A → Set b) {x y : A} (p : x ≡ y) → B x → B y
transport1 B p = run (ap B p)

ap-const : ∀ {a b} {A : Set a} {B : Set b} (f : B) {a₁ a₂ : A} (p : a₁ ≡ a₂) → ap (\ _ → f) p ≡ refl
ap-const f refl = refl
{-# REWRITE ap-const #-}

ap2 : ∀ {a b rv} {A : Set a} {B : A → Set b} {RV : Set rv} (fn : ∀ a → B a → RV) {a₁ a₂} (pa : a₁ ≡ a₂) {b₁ b₂} (pb : transport1 B pa b₁ ≡ b₂) → fn a₁ b₁ ≡ fn a₂ b₂
ap2 fn refl refl = refl

transport2 : ∀ {a b rv} {A : Set a} {B : A → Set b} (RV : ∀ a → B a → Set rv) {a₁ a₂} (pa : a₁ ≡ a₂) {b₁ b₂} (pb : transport1 B pa b₁ ≡ b₂) → RV a₁ b₁  → RV a₂ b₂
transport2 RV pa pb = run (ap2 RV pa pb)

ap2-const : ∀ {a b rv} {A : Set a} {B : A → Set b} {RV : Set rv} (fn : RV) {a₁ a₂} (pa : a₁ ≡ a₂) {b₁ b₂} (pb : transport1 B pa b₁ ≡ b₂) → ap2 {a} {b} {rv} {A} {B} {RV} (λ _ _ → fn) pa pb ≡ refl
ap2-const fn refl refl = refl
{-# REWRITE ap2-const #-}

ap2-const' : ∀ {a b rv} {A : Set a} {B : A → Set b} {RV : Set rv} (fn : RV) {a₁ a₂} (pa : a₁ ≡ a₂) {b₁ b₂} (pb : transport1 B pa b₁ ≡ b₂) → ap2 {a} {b} {rv} {A} {B} {RV} (λ _ _ → fn) pa pb ≡ refl
ap2-const' {a} {b} {rv} {A} {B} {RV} fn pa pb = {!ap2 {a} {b} {_} {A} {_} {_} (λ _ _ → fn ≡ fn) pa _!}
