
open import Agda.Primitive
open import Agda.Builtin.Equality

variable
  ℓ : Level
  A : Set ℓ
  P : A → Set ℓ
  x y : A
  f : (x : A) → P x

cong : x ≡ y → f x ≡ f y
cong refl = refl
