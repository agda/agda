{-# OPTIONS --warning ShadowingInTelescope --allow-unsolved-metas #-}

open import Agda.Primitive

-- warning here
data _~_ {a a : Level} {A : Set a} (a : A) : A -> Set where
  refl : a ~ a

module _ {a} {A : Set a} where

-- nothing: the repetition is in separate telescopes
  data Eq (a : A) : (a : A) → Set where
    refl : Eq a a

-- warning here
f : ∀ (a : Level) → ∀ {A : Set a} A ~ A → Set → Set
f a A ~ B = λ x → x

-- nothing here: the repetition is in separate telescopes
f' : ∀ a → Set a → Set a
f' a = g a where

  g : ∀ a → Set a → Set a
  g a z = z

-- nothing here: the variable {a} is not user-written
h : ∀ {a} → Set a → Set a
h = g _ where

  g : ∀ a → Set a → Set a
  g a z = z


i : (Set → Set → Set) → (∀ _ _ → _)
i f = f
