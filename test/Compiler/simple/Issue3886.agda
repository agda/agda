-- Andreas, 2019-07-04, issue #3886
-- Override forcing with explicit quantity attributes.

{-# OPTIONS --erasure #-}

open import Common.Prelude

pattern [_] x = x ∷ []

module _ {a} {A : Set a} where

  variable
    x y z : A
    @0 xs ys zs : List A

  data FSet : List A → Set a where
    ∅   : FSet []
    _∪_ : FSet xs → FSet ys → FSet (xs ++ ys)
    sg  : (@ω x : A) → FSet [ x ]
    -- x is forced here, but this is not wanted.
    -- With an explicit quantity attribute we tell the forcing machinery not to erase x.

  -- Since xs is erased, we cannot get x from sg x : FSet xs (with xs = [ x ])
  -- unless x is retained in sg x.
  elements : {@0 xs : List A} → FSet xs → List A
  elements ∅       = []
  elements (s ∪ t) = elements s ++ elements t
  elements (sg x)  = [ x ]

-- ERROR WAS:
-- Variable x is declared erased, so it cannot be used here
-- when checking that the expression x has type A

mySet = (sg 1 ∪ sg 2) ∪ (sg 3 ∪ sg 4)

sum : List Nat → Nat
sum [] = 0
sum (n ∷ ns) = n + sum ns

test = elements mySet

main = printNat (sum (elements mySet))

-- Should print 10.
