
record Additive {ℓ} (A : Set ℓ) : Set ℓ where
  field
    zero : A
    _+_ : A → A → A

open Additive {{...}} public

record Subtractive {ℓ} (A : Set ℓ) {{ADD : Additive A}} : Set ℓ where
  field
    _-_ : A → A → A

  neg : A → A
  neg x = zero - x

open Subtractive {{...}} public

check : ∀ ℓ (A : Set ℓ) (ADD : Additive A) (SUB : Subtractive A {{ADD}}) → A → A
check ℓ A ADD SUB x = Subtractive.neg {ℓ} {A} {{ADD}} SUB x
