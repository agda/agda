-- Andreas, 2019-08-07, issue #3966
--
-- Precise error location for unification problem during coverage checking.

{-# OPTIONS --without-K #-}

module _ {A : Set} where

open import Common.Equality
open import Common.List

data _⊆_ : (xs ys : List A) → Set where
  _∷ʳ_ : ∀ {xs ys} → ∀ y → _⊆_ xs ys → _⊆_ xs (y ∷ ys)
  _∷_  : ∀ {x xs y ys} → x ≡ y → _⊆_ xs ys → _⊆_ (x ∷ xs) (y ∷ ys)

⊆-trans : ∀{xs ys zs} → xs ⊆ ys → ys ⊆ zs → xs ⊆ zs
⊆-trans rs        (y ∷ʳ ss) = y ∷ʳ ⊆-trans  rs ss
⊆-trans (y ∷ʳ rs) (s ∷ ss)  = _ ∷ʳ ⊆-trans  rs ss
⊆-trans (r ∷ rs)  (s ∷ ss)  = trans r s ∷ ⊆-trans rs ss

-- Provoke a unification error during coverage checking:

test : ∀ {x} {xs ys zs : List A} {τ : (x ∷ xs) ⊆ zs} {σ : ys ⊆ zs}
       us (ρ : us ⊆ zs) (τ' : (x ∷ xs) ⊆ us) (σ' : ys ⊆ us)
       (σ'∘ρ≡σ : ⊆-trans σ' ρ ≡ σ)
       → Set₁

test {τ = z ∷ʳ τ} {σ = z ∷ʳ σ} (y ∷ us) (.z ∷ʳ ρ) (y ∷ʳ τ') (refl ∷ σ') refl = Set
test {σ = z ∷ʳ σ} _ (refl ∷ ρ) _ (refl ∷ σ') ()
test {τ = z   ∷ʳ τ} {σ = refl ∷ σ} (y ∷ us) ρ (y ∷ʳ τ') (refl ∷ σ') σ'∘ρ≡σ = Set
test {τ = refl ∷ τ} {σ = z   ∷ʳ σ} (y ∷ us) ρ (y ∷ʳ τ') (refl ∷ σ') σ'∘ρ≡σ = Set
test {τ = refl ∷ τ} {σ = refl ∷ σ} (y ∷ us) ρ (y ∷ʳ τ') (refl ∷ σ') σ'∘ρ≡σ = Set

test (x ∷ us) ρ (refl ∷ τ') (x ∷ʳ σ') refl = Set  -- ONLY this LHS should be highlighted!
test (x ∷ us) ρ (refl ∷ τ') (refl ∷ σ') σ'∘ρ≡σ = Set
test (y ∷ us) ρ (y ∷ʳ τ') (refl ∷ σ') σ'∘ρ≡σ =  Set

-- Expected error location: 34,1-43

-- I'm not sure if there should be a case for the constructor refl,
-- because I get stuck when trying to solve the following unification
-- problems (inferred index ≟ expected index):
--   ⊆-trans (x ∷ʳ σ') ρ ≟ refl ∷ σ
-- when checking the definition of test
