
open import Agda.Builtin.Nat
open import Agda.Builtin.Equality

record Eq (A : Set) : Set₁ where
  field
    _≈_ : A → A → Set

open Eq {{...}} public

record Setoid : Set₁ where
  field
    ∣_∣    : Set
    {{eq}} : Eq ∣_∣

open Setoid public

-- instance
--   EqNat : Eq Nat
--   _≈_ {{EqNat}} = _≡_

NatSetoid : Setoid
∣ NatSetoid ∣ = Nat
-- Should give: No instance of type Eq Nat
