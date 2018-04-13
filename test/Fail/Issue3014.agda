
data Bool : Set where
  true false : Bool

data Eq : Bool → Bool → Set where
  refl : (x : Bool) → Eq x x

test : (x : Bool) → Eq true x → Set
test _ (refl false) = Bool
