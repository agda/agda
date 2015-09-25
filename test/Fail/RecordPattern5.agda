-- Andreas, 2015-07-20, record patterns

open import Common.Prelude

postulate A : Set

record R : Set where
  field f : A

T : Bool → Set
T true  = R
T false = A

test : ∀{b} → T b → A
test record{f = a} = a

-- Could succeed by some magic.
