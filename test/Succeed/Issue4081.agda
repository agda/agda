open import Agda.Builtin.Equality

module _ (A : Set) where

data Wrap (X : Set) : Set where
  wrap : X → Wrap X

data D (x : A) : ∀ y → Wrap (x ≡ y) → Set where
  c : ∀ y (x≡y : x ≡ y) → D x y (wrap x≡y)

test : ∀ x y (x≡y x≡y' : Wrap (x ≡ y)) → D x y x≡y → D x y x≡y' → Set
test y .y (wrap refl) .(wrap refl) (c .y .refl) (c .y refl) = A
