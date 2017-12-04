-- Andreas, 2017-12-04, Re: issue #2862, reported by m0davis,
-- Make sure there is similar problem with functions.

open import Agda.Builtin.Equality

data Bool : Set where
  true false : Bool

module N where
  val : Bool  -- Should fail

module M where
  open N
  val = true
  val≡true : val ≡ true
  val≡true = refl

open N
val = false

data ⊥ : Set where

¬val≡true : val ≡ true → ⊥
¬val≡true ()

-- val≡true : val ≡ true
-- val≡true = Z.va val true

boom : ⊥
boom = ¬val≡true Z.val≡true
