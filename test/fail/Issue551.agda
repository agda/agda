-- Andreas, 2012-01-11, bug reported by Adam Gundry
module Issue551 where

data Bool : Set where
  true false : Bool

data _≡_ {A : Set}(a : A) : A → Set where
  refl : a ≡ a

cong : {A B : Set}(f : A → B){a a' : A} → a ≡ a' → f a ≡ f a'
cong f refl = refl

implicit : {A : Set}{{a : A}} -> A
implicit {{a}} = a

record PackBool : Set where
  constructor pack
  field unpack : Bool
open PackBool

data IrrBool : Set where
  irr : .(b : PackBool) -> IrrBool 

p : irr (pack true) ≡ irr (pack false)
p = refl

-- The following should fail:

unirr : IrrBool -> PackBool
unirr (irr x) = implicit
-- unirr (irr x) = x gives an error message (as well it should)
-- but using instance arguments circumvents the check.

q : true ≡ false
q = cong (λ x → unpack (unirr x)) p
 