{-# OPTIONS --cohesion --type-in-type #-}

module _ where

open import Agda.Builtin.Equality

record Sharp (@♯ A : Set) : Set where
  constructor con
  field
    @♯ counit : A

open Sharp

unit : {A : Set} → A → Sharp A
unit x = con x

ind : ∀ {A : Set} (B : Sharp A → Set)
        → (f : (a : A) → Sharp (B (unit a)))
        → (a : Sharp A) → Sharp (B a)
ind B f x .counit = f (x .counit) .counit

mult : {A : Set} → Sharp (Sharp A) → Sharp A
mult a .counit = a .counit .counit

_ : ∀ {@♭ A : Set} → @♭ (Sharp A) → A
_ = counit

-- Sharp also makes module variables crisp
module _ {A : Set} (P : @♭ Set → Set) where
  test : Sharp Set
  test .counit = P A

-- Eta rules for Sharp
_ : ∀ {@♭ A : Set} {@♭ x : A} → counit (con x) ≡ x
_ = refl

_ : ∀ {A : Set} {x : Sharp A } → con (counit x) ≡ x
_ = refl
