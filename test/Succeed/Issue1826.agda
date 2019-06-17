-- Andreas, 2016-02-09, issue and test case by Nisse

{-# OPTIONS --allow-unsolved-metas #-}

open import Common.Level

postulate
  _≡_  : ∀ {a} {A : Set a} → A → A → Set a
  refl : ∀ {a} {A : Set a} (x : A) → x ≡ x

record R a p : Set (lsuc (a ⊔ p)) where
  field
    elim : {A : Set a} (P : {x y : A} → x ≡ y → Set p) →
           (∀ x → P (refl x)) →
           ∀ {x y} (x≡y : x ≡ y) → P x≡y

module _ (eq : ∀ {a p} → R a p) where

  open module M {a p} = R (eq {a} {p})

  postulate

    elim-refl   : ∀ {a p} {A : Set a} (P : {x y : A} → x ≡ y → Set p)
                  (r : ∀ x → P (refl x)) {x} →
                  elim P r (refl x) ≡ r x
    cong        : ∀ {a b} {A : Set a} {B : Set b}
                  (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
    subst       : ∀ {a p} {A : Set a} (P : A → Set p) {x y : A} →
                  x ≡ y → P x → P y
    subst-refl  : ∀ {a p} {A : Set a} (P : A → Set p) {x} (p : P x) →
                  subst P (refl x) p ≡ p
    trans       : ∀ {a} {A : Set a} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
    cong₂       : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c}
                  (f : A → B → C) {x y : A} {u v : B} →
                  x ≡ y → u ≡ v → f y v ≡ f x u
    trans-reflʳ : ∀ {a} {A : Set a} {x y : A} (x≡y : x ≡ y) →
                  trans x≡y (refl y) ≡ x≡y
    trans-reflˡ : ∀ {a} {A : Set a} {x y : A} (x≡y : x ≡ y) →
                  trans (refl x) x≡y ≡ x≡y

  [subst≡]≡[trans≡trans] :
    ∀ {a} {A : Set a} {x y : A} {p : x ≡ y} {q : x ≡ x} {r : y ≡ y} →
    (subst (λ z → z ≡ z) p q ≡ r)
      ≡
    (trans q p ≡ trans p r)
  [subst≡]≡[trans≡trans] {p = p} {q} {r} = elim
    (λ {x y} p → {q : x ≡ x} {r : y ≡ y} →
                 (subst (λ z → z ≡ z) p q ≡ r)
                   ≡
                 (trans q p ≡ trans p r))
    (λ x {q r} →
       trans (cong (λ x → x ≡ _) (subst-refl (λ z → z ≡ z) _))
             (cong₂ _≡_ (trans-reflʳ _) (trans-reflˡ _)))
    p

  foo :
    ∀ {a} {A : Set a} {x : A} {q : x ≡ x} {r : x ≡ x} →
    [subst≡]≡[trans≡trans] {p = refl x} {q = q} {r = r} ≡
    [subst≡]≡[trans≡trans] {p = refl x} {q = q} {r = r}
  foo = elim-refl ? ?
