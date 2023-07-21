-- Andreas, 2023-05-29, issue #6594
-- Temporary regression in 2.6.4 (unreleased) reported by @nad.
-- Fixed by reverting type-directed occurs check.

record R : Set₁ where
  field
    _≡_         : {A : Set} → A → A → Set
    refl        : {A : Set} (x : A) → x ≡ x
    sym         : {A : Set} {x y : A} → x ≡ y → y ≡ x
    trans       : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
    cong        : {A B : Set} {x y : A}
                  (f : A → B) → x ≡ y → f x ≡ f y
    cong-refl   : {A B : Set} {x : A} (f : A → B) →
                  cong f (refl x) ≡ refl (f x)
    subst       : {A : Set} {x y : A} (P : A → Set) →
                  x ≡ y → P x → P y
    subst-subst : {A : Set} {x y z : A} {x≡y : x ≡ y} {y≡z : y ≡ z}
                  {P : A → Set} {p : P x} →
                  subst P y≡z (subst P x≡y p) ≡
                  subst P (trans x≡y y≡z) p

  f :
    {A : Set} {x y z : A} {x≡y : x ≡ y} {y≡z : y ≡ z}
    {P : A → Set} {p : P x} {q : P z}
    {p≡q : subst P y≡z (subst P x≡y p) ≡ q} →
    trans (sym subst-subst) (trans (cong (subst P y≡z) (refl _)) p≡q) ≡
    trans (sym subst-subst) (trans (refl _) p≡q)
  f = cong (λ x → trans (sym subst-subst) (trans x _)) (cong-refl _)

-- Should succeed.
