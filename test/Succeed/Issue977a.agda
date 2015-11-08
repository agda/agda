-- Andreas, 2013-11-23
-- checking that postulates are allowed in new-style mutual blocks

open import Common.Prelude

-- new style mutual block

even : Nat → Bool

postulate
  odd : Nat → Bool

even zero    = true
even (suc n) = odd n

-- No error
