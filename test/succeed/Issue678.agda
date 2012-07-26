-- Andreas, 2012-07-26, reported by Nisse
module Issue678 where

module Unit where

  data Unit : Set where
    unit : Unit

  El : Unit → Set
  El unit = Unit

  data IsUnit : Unit → Set where
    isUnit : IsUnit unit

  test : (u : Unit)(x : El u)(p : IsUnit u) → Set
  test .unit unit isUnit = Unit
  -- this requires the coverage checker to skip the first split opportunity, x,
  -- and move on to the second, p

module NisseOriginalTestCase where

  record Box (A : Set) : Set where
    constructor [_]
    field unbox : A

  data U : Set where
    box : U → U

  El : U → Set
  El (box a) = Box (El a)

  data Q : ∀ a → El a → El a → Set where
    q₁ : ∀ {a x} → Q (box a) [ x ] [ x ]
    q₂ : ∀ {a} {x y : El a} → Q a x y

  data P : ∀ a → El a → El a → Set where
    p : ∀ {a x y z} → P a x y → P a y z → P a x z

  foo : ∀ {a xs ys} → P a xs ys → Q a xs ys
  foo (p p₁ p₂) with foo p₁ | foo p₂
  foo (p p₁ p₂) | q₁ | _ = q₂
  foo (p p₁ p₂) | q₂ | _ = q₂

-- Error was:
-- Cannot split on argument of non-datatype El @1
-- when checking the definition of with-33
