-- Andreas, 2013-11-07
-- Need to drop parameters not only from constructors found by
-- instance search, but also from projection(like) functions.
module Issue670b where

open import Common.Prelude
open import Common.Equality

record Wrap (A : Set) : Set where
  constructor wrap
  field
    unwrap : A
open Wrap

module _ {A : Set} where

  g : {{i : Wrap A → A}} → Wrap A → A
  g {{i}} = i

test : g (wrap true) ≡ true
test = refl

-- Error WAS:
-- unwrap Bool (wrap true) != true of type Bool
-- when checking that the expression refl has type
-- g (wrap true) ≡ true

-- Should work now.
