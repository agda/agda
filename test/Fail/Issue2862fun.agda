-- Andreas, 2017-12-04, Re: issue #2862, reported by m0davis,
-- Make sure there is similar problem with functions.

open import Agda.Builtin.Equality

data Bool : Set where
  true false : Bool

val : Bool

module M where
  val = true  -- Should fail

  val≡true : val ≡ true
  val≡true = refl

val = false

data ⊥ : Set where

¬val≡true : val ≡ true → ⊥
¬val≡true ()

boom : ⊥
boom = ¬val≡true Z.val≡true
