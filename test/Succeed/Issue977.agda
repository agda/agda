-- Andreas, 2013-11-23
-- postulates are now alsow allowed in old-style mutual blocks

open import Common.Prelude

mutual
  even : Nat → Bool
  even zero    = true
  even (suc n) = odd n

  postulate
    odd : Nat → Bool

-- Error WAS: Postulates are not allowed in mutual blocks

-- Andreas, 2023-09-27, issue #1702
-- Allow 'private' in postulates

postulate
  private
    Foo : Set
