-- The following code triggered an internal error when the master
-- branch was merged incorrectly into the issue4067 branch.

open import Agda.Builtin.Sigma

record R : Set₁ where
  field
    _≡_        : {A : Set} → A → A → Set
    refl       : {A : Set} (x : A) → x ≡ x
    trans      : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
    cong       : {A B : Set} {x y : A}
                 (f : A → B) → x ≡ y → f x ≡ f y
    subst      : {A : Set} {x y : A} (P : A → Set) →
                 x ≡ y → P x → P y
    subst-refl : ∀ {A : Set} {x} (P : A → Set) p →
                 subst P (refl x) p ≡ p

  Contractible : Set → Set
  Contractible A = Σ A λ x → ∀ y → x ≡ y

  Singleton : {A : Set} → A → Set
  Singleton x = Σ _ λ y → y ≡ x

  field

    prop : {A : Set} {x : A} (p : Singleton x) → (x , refl x) ≡ p

  singleton-contractible :
    {A : Set} (x : A) → Contractible (Singleton x)
  singleton-contractible x = ((x , refl x) , prop)

  field

    singleton-contractible-refl :
      {A : Set} (x : A) →
      snd (singleton-contractible x) (x , refl x) ≡ refl (x , refl x)

  J :
    {A : Set} {x y : A}
    (P : {x : A} → x ≡ y → Set) →
    P (refl y) →
    (x≡y : x ≡ y) → P x≡y
  J {x = x} {y = y} P p x≡y =
    subst (λ p → P (snd p))
          (snd (singleton-contractible y) (x , x≡y))
          p

  J-refl :
    {A : Set} {y : A}
    (P : ∀ {x} → x ≡ y → Set) (p : P (refl y)) →
    J P p (refl y) ≡ p
  J-refl {y = y} P p =
    trans (cong (λ q → subst (λ p → P (snd p)) q _)
                (singleton-contractible-refl _))
          (subst-refl _ _)
