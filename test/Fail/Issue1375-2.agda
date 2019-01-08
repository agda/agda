-- Andreas, 2014-12-02, issue reported by Jesper Cockx
{-# OPTIONS --no-guardedness #-}

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

subst : ∀ (A : Set)(P : A → Set)(x y : A) → x ≡ y → P x → P y
subst A P x .x refl t = t

mutual
  Type : Set
  postulate
    type : Type
    Term : Type → Set

  Type = Term type

mutual
  weakenType : Type → Type → Type
  weaken : (ty ty' : Type) → Term ty → Term (weakenType ty' ty)

  weakenType ty ty' =
    let X : Type
        X = {!!}
    in  subst Type Term (weakenType X type) type {!!} (weaken type X ty)
  weaken ty ty' t = {!!}

data Test : Type → Set where
  test : Test (weakenType type type)

-- Checking the constructor declaration was looping
-- should work now.
