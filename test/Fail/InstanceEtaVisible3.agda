module InstanceEtaVisible3 where

data _≡_ {A : Set} (a : A) : A -> Set where
    refl : a ≡ a

÷_ : ∀ {A : Set} {a1 a2 : A} -> (a1 ≡ a2) -> (a2 ≡ a1)
÷ refl = refl

record Mul (A : Set) : Set where
  field
    _*_ : A → A → A
open Mul ⦃ ... ⦄

record Semimonoid : Set₁ where
  field
    carrier : Set
    ⦃ g ⦄   : Mul carrier
    right-assoc : ∀ (x y z : carrier) -> ((x * y) * z) ≡ (x * (y * z))
open Semimonoid

left-assoc : (M : Semimonoid) (x y z : M .carrier) → (x * (y * z)) ≡ ((x * y) * z)
left-assoc M x y z = ÷ (right-assoc M x y z)
