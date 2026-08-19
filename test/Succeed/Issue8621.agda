-- Andreas, 2026-08-19, issue #8621, reported and test by Elisabeth Stenholm
-- An internal error in 2.8.0 already fixed on 2.9.0 master.

{-# OPTIONS --allow-unsolved-metas #-}

open import Agda.Primitive

data _≡_ {ℓ} {A : Set ℓ} (a : A) : A → Set ℓ where
  refl : a ≡ a

record isSet {ℓ} (A : Set ℓ) : Set ℓ where
  field uip : (x y : A) (p q : x ≡ y) → p ≡ q

record SetQuotient {i a} (X : Set i) (R : X → X → Set a) : Setω where
  field
    Quotient : Set (i ⊔ a)
    [_]      : X → Quotient
    ⦃ set ⦄  : isSet Quotient
    respects : ∀ {x y} → R x y → [ x ] ≡ [ y ]
    rec      : ∀ {j} {B : Set j} ⦃ bset : isSet B ⦄
             → (f : X → B) → (∀ {x y} → R x y → f x ≡ f y) → Quotient → B
    rec-β    : ∀ {j} {B : Set j} ⦃ bset : isSet B ⦄
                 {f : X → B} {resp : ∀ {x y} → R x y → f x ≡ f y} {x : X}
             → rec f resp [ x ] ≡ f x

_⁄_ : ∀ {i a} (X : Set i) (R : X → X → Set a) ⦃ w : SetQuotient X R ⦄ → Set (i ⊔ a)
(X ⁄ R) ⦃ w = w ⦄ = SetQuotient.Quotient w

[_] : ∀ {i a} {X : Set i} {R : X → X → Set a} ⦃ w : SetQuotient X R ⦄ → X → X ⁄ R
[_] ⦃ w = w ⦄ = SetQuotient.[_] w

respects : ∀ {i a} {X : Set i} {R : X → X → Set a} ⦃ w : SetQuotient X R ⦄
         → ∀ {x y} → R x y → [ x ] ≡ [ y ]
respects ⦃ w = w ⦄ = SetQuotient.respects w

rec : ∀ {i a j} {X : Set i} {R : X → X → Set a} ⦃ w : SetQuotient X R ⦄
        {B : Set j} ⦃ bset : isSet B ⦄
    → (f : X → B) → (∀ {x y} → R x y → f x ≡ f y) → X ⁄ R → B
rec ⦃ w = w ⦄ = SetQuotient.rec w

rec-β : ∀ {i a j} {X : Set i} {R : X → X → Set a} ⦃ w : SetQuotient X R ⦄
          {B : Set j} ⦃ bset : isSet B ⦄
          {f : X → B} {resp : ∀ {x y} → R x y → f x ≡ f y} {x : X}
      → rec f resp [ x ] ≡ f x
rec-β ⦃ w = w ⦄ = SetQuotient.rec-β w

record AllSetQuotients : Setω where
  field quotient : ∀ {i a} (X : Set i) (R : X → X → Set a) → SetQuotient X R

module FromAllSetQuotients {i a} (X : Set i) (R : X → X → Set a) ⦃ w : AllSetQuotients ⦄ where
  instance
    setQuotient : SetQuotient X R
    setQuotient = AllSetQuotients.quotient w X R
    setQuotient-isSet : isSet (SetQuotient.Quotient setQuotient)
    setQuotient-isSet = SetQuotient.set setQuotient

module _ ⦃ _ : AllSetQuotients ⦄ {i a : Level}
         (X : Set i) (R : X → X → Set a)
         (Y : Set i) (S : Y → Y → Set a)
         (h : X → Y) (r : ∀ {x y} → R x y → S (h x) (h y)) where
  open FromAllSetQuotients X R hiding (setQuotient-isSet)
  open FromAllSetQuotients Y S

  toQuot : X ⁄ R → Y ⁄ S
  toQuot = rec (λ x → [ h x ]) (λ ρ → respects (r ρ))

  toQuotβ : (x : X) → toQuot [ x ] ≡ [ h x ]
  toQuotβ x = rec-β
