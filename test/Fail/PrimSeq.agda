
module _ where

open import Common.Prelude
open import Common.Equality

primitive primForce : ∀ {a b} {A : Set a} {B : A → Set b} (x : A) → (∀ x → B x) → B x

force = primForce

not-stuck : (b : Bool) → force b not ≡ not b
not-stuck true = refl
not-stuck false = refl

stuck : (b : Bool) → force b not ≡ not b
stuck b = refl
