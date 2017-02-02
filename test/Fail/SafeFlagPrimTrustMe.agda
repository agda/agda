module SafeFlagPrimTrustMe where

open import Agda.Builtin.Equality

private
 primitive
   primTrustMe : ∀ {a} {A : Set a} {x y : A} → x ≡ y
