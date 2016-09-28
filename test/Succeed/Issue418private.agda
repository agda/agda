-- Andreas, 2016-07-19 revisiting issue #418

module Issue418private where

open import Common.Equality

abstract

  A : Set₁
  A = Set

  private
    works : A ≡ A
    works = refl

    test : A ≡ _
    test = refl

-- Since test is private, abstract definitions are transparent in its type.
-- The meta should be solved (by A or Set).
