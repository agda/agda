module _ where

open import Agda.Builtin.Equality

postulate
  A : Set
  P : A → Set

data Id (A : Set) : Set where
  id : A → Id A

data Flat (@♭ A : Set) : Set where
  con : (@♭ x : A) → Flat A

counit : {@♭ A : Set} → Flat A → A
counit (con x) = x

test2 : (@♭ x : Id A) → Flat A
test2 (id x) = con x

test3 : (@♭ x : A) (@♭ y : A) (@♭ p : x ≡ y) → P x → P y
test3 x y refl p = p

test4 : (@♭ x : A) (@♭ y : A) → Flat (x ≡ y) → P x → P y
test4 x y (con refl) p = p

test6 : (@♭ x y : A) → (eq : con x ≡ con y) → P x → P y
test6 x .x refl p = p
