------------------------------------------------------------------------
-- The Agda standard library
--
-- Experimental, postulated quotients with a computing eliminator
-- (possibly unsound)
------------------------------------------------------------------------

module Quotient where

open import Level
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as P using (_≡_)
open P.≡-Reasoning

private
 module Dummy where

  -- Quotients are parametrised by setoids.
  --
  -- It is perhaps wise to only use this construction with
  -- proof-irrelevant setoids.

  data Quotient {c ℓ} (A : Setoid c ℓ) : Set (c ⊔ ℓ) where
    box : (x : Setoid.Carrier A) → Quotient A

 open Dummy public using (Quotient)

-- The constructor is not exported: users are not allowed to
-- pattern match without using the eliminator below.

[_] : ∀ {c ℓ} {A : Setoid c ℓ} → Setoid.Carrier A → Quotient A
[_] = Dummy.box

-- [_] is postulated to respect equality. This could be unsound.

postulate
  [_]-cong : ∀ {c ℓ} {A : Setoid c ℓ} {a₁ a₂} → let open Setoid A in
             a₁ ≈ a₂ → _≡_ {A = Quotient A} [ a₁ ] [ a₂ ]

-- Elements in equal equivalence classes are related.

[_]-cong⁻¹ : ∀ {c ℓ} {A : Setoid c ℓ} {a₁ a₂} → let open Setoid A in
             _≡_ {A = Quotient A} [ a₁ ] [ a₂ ] → a₁ ≈ a₂
[_]-cong⁻¹ {A = A} P.refl = Setoid.refl A

-- Eliminator.

elim : ∀ {c ℓ p} (A : Setoid c ℓ) → let open Setoid A in
       (P : Quotient A → Set p)
       (f : (x : Carrier) → P [ x ]) →
       (∀ {x y} (x≈y : x ≈ y) → P.subst P [ x≈y ]-cong (f x) ≡ f y) →
       ∀ c → P c
elim _ P f _ (Dummy.box x) = f x

-- Non-dependent eliminator.

rec : ∀ {c ℓ p} (A : Setoid c ℓ) {P : Set p} → let open Setoid A in
      (f : (x : Carrier) → P) →
      (∀ {x y} (x≈y : x ≈ y) → f x ≡ f y) →
      Quotient A → P
rec _ {P = P} f cong =
  elim _ (λ _ → P) f
       (λ {x y} x≈y → begin
          P.subst (λ _ → P) [ x≈y ]-cong (f x)  ≡⟨ lemma [ x≈y ]-cong (f x) ⟩
          f x                                   ≡⟨ cong x≈y ⟩
          f y                                   ∎)
  where
  lemma : ∀ {a p} {A : Set a} {P : Set p} {x y : A}
          (x≡y : x ≡ y) (p : P) →
          P.subst (λ _ → P) x≡y p ≡ p
  lemma P.refl _ = P.refl
