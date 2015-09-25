
import Common.Reflection

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

data Bool : Set where
  true false : Bool

data True : Set where
  true : True

-- Should print names as "quote Bool.true" (making sure to disambiguate)
-- and "quote false" rather than "Issue619.Bool.true/false" in error message.
not-true : quote Bool.true ≡ quote Bool.false
not-true = refl
