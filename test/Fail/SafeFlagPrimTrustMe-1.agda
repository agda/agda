module SafeFlagPrimTrustMe-1 where

open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Erase

private
  postulate
    unsafePrimTrustMe : ∀ {a} {A : Set a} {x y : A} → x ≡ y

primTrustMe : ∀ {a} {A : Set a} {x y : A} → x ≡ y
primTrustMe = primEraseEquality unsafePrimTrustMe
