module Issue462 where

data _≡_ {A : Set} : A → A → Set where
  ≡-refl : (x : A) → x ≡ x

postulate A : Set

record R (_≈_ _∼_ : A → A → Set) : Set where
  field
    ≈-refl      : (x : A) → x ≈ x
    ∼-reflexive : (x y : A) → x ≈ y → x ∼ y

  ∼-refl : (x : A) → x ∼ x
  ∼-refl x = ∼-reflexive x x (≈-refl x)

postulate
  _≈_    : A → A → Set
  ≈-refl : ((x : A) → x ≡ x) → (x : A) → x ≈ x
  ≈-irr  : (x : A) (p : x ≈ x) → p ≡ p

≡-r : R _≡_ _≡_
≡-r = record
  { ≈-refl      = ≡-refl
  ; ∼-reflexive = λ _ _ p → p
  }

≈-reflexive : (x y : A) → x ≡ y → x ≈ y
≈-reflexive .x .x (≡-refl x) = ≈-refl (R.∼-refl ≡-r) x

≈-r : R _≡_ _≈_
≈-r = record
  { ≈-refl      = ≡-refl
  ; ∼-reflexive = ≈-reflexive
  }

foo : A → Set₁
foo x with ≈-irr x (R.∼-refl ≈-r x)
foo x | _ = Set

-- The generated with function should not contain unsolved
-- meta-variables.
