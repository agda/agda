
open import Agda.Builtin.Char
open import Agda.Builtin.List
open import Agda.Builtin.Equality
open import Agda.Builtin.String
open import Agda.Builtin.String.Properties

data ⊥ : Set where

∷⁻¹ : ∀ {A : Set} {x y : A} {xs ys} → x ∷ xs ≡ y ∷ ys → x ≡ y
∷⁻¹ refl = refl

xD800 = primNatToChar 0xD800
xD801 = primNatToChar 0xD801

legit : '\xD800' ∷ [] ≡ '\xD801' ∷ []
legit = primStringFromListInjective _ _ refl

actually : xD800 ≡ xD801
actually = refl

nope : xD800 ≡ xD801 → ⊥
nope ()

boom : ⊥
boom = nope (∷⁻¹ legit)

errorAlsoInLHS : Char → String
errorAlsoInLHS '\xD8AA' = "bad"
errorAlsoInLHS _        = "meh"
