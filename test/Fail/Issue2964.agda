open import Agda.Builtin.Bool
open import Agda.Builtin.Equality

record R : Set₁ where
  field
    fun  : (A : Set) → A → Bool → A ≡ Bool → Bool
    rule : ∀ x → fun Bool false x refl ≡ false
open R

test : R
fun test .Bool true true refl = true
fun test _     _    _    _    = false
rule test x = refl
