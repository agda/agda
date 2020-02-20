open import Agda.Primitive using (Level; lsuc)

variable
  ℓ p   : Level
  A B   : Set ℓ
  x y z : A

postulate
  easy : A

record R a : Set (lsuc a) where
  field
    _≡_ : {A : Set a} → A → A → Set a

module _ (r : ∀ ℓ → R ℓ) where

  open module R′ {ℓ} = R (r ℓ)

  postulate
    refl      : (x : A) → x ≡ x
    cong      : (f : A → B) → x ≡ y → f x ≡ f y
    subst     : (P : A → Set p) → x ≡ y → P x → P y
    trans     : x ≡ y → y ≡ z → x ≡ z
    elim      : (P : {x y : A} → x ≡ y → Set p) →
                (∀ x → P (refl x)) →
                (x≡y : x ≡ y) → P x≡y
    elim-refl : (P : {x y : A} → x ≡ y → Set p)
                (r : ∀ x → P (refl x)) →
                elim P r (refl x) ≡ r x

  [subst≡]≡[trans≡trans] :
    {p : x ≡ y} {q : x ≡ x} {r : y ≡ y} →
    (subst (λ z → z ≡ z) p q ≡ r)
      ≡
    (trans q p ≡ trans p r)
  [subst≡]≡[trans≡trans] {p = p} {q} {r} = elim
    (λ {x y} p → {q : x ≡ x} {r : y ≡ y} →
                 (subst (λ z → z ≡ z) p q ≡ r)
                   ≡
                 (trans q p ≡ trans p r))
    (λ _ → easy)
    p

  [subst≡]≡[trans≡trans]-refl :
    {q r : x ≡ x} →
    [subst≡]≡[trans≡trans] {p = refl x} {q = q} {r = r} ≡
    easy
  [subst≡]≡[trans≡trans]-refl {q = q} {r = r} =
    cong (λ f → f {q = q} {r = r})
      (elim-refl (λ {x y} _ → {q : x ≡ x} {r : y ≡ y} → _) _)
