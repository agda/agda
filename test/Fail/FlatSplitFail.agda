module _ where

open import Agda.Builtin.Equality

postulate
  A : Set
  P : A → Set

data Flat (@♭ A : Set) : Set where
  con : (@♭ x : A) → Flat A

-- it should not be able to unify x and y,
-- because the equality is not @♭.
test4 : (@♭ x : A) (@♭ y : A) → (x ≡ y) → P x → P y
test4 x y refl p = {!!}
