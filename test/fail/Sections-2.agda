open import Common.Prelude

postulate
  foo_bar_ : (b : Bool) → if b then Nat else Bool → Set

Test : Set
Test = foo_bar 5
