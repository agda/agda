module _ (X : Set) where

open import Agda.Builtin.Equality

postulate
  A : Set

data D : Set where
  c : A → D

variable
  P : D → Set

postulate
  p : (f : ∀ x → P (c x)) (x y : A) → f x ≡ f y
