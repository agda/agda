-- As reported by Andreas on 2017-01-23

open import Common.Equality
open import Common.Product

data Bool : Set where
  true false : Bool

f : (x y : Bool) → Bool
f true y     = y
-- f false x = true  -- Missing case

test : let
     X : Bool → Bool → Bool
     X = {! f !}
  in (∀{x y} → X (f false x) y ≡ y) × (X false false ≡ true)
test = refl , refl

-- If we add the missing clause f false x = true, then X has
-- for instance solution f.
