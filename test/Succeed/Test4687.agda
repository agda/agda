
open import Agda.Primitive
open import Agda.Builtin.List
open import Agda.Builtin.Maybe

data Coercible (A : Set) (B : Set) : Set where
  TrustMe : Coercible A B

postulate coerce : {A B : Set} {{_ : Coercible A B}} → A → B

instance
  coerce-fun : {A B : Set} {{_ : Coercible A B}}
             → {C D : Set} {{_ : Coercible C D}}
             → Coercible (B → C) (A → D)
  coerce-fun = TrustMe

  coerce-refl : {A : Set} → Coercible A A
  coerce-refl = TrustMe

postulate
  primCatMaybes : {A : Set} → List (Maybe A) → List A

catMaybes : {A : Set} → List (Maybe A) → List A
catMaybes = coerce (primCatMaybes {_})
