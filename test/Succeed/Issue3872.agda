-- Andreas, 2019-06-26, issue #3872, make --no-forcing a pragma option

{-# OPTIONS --no-forcing #-}

open import Agda.Builtin.Nat

data List {a} (A : Set a) : Set a where
  [] : List A
  _∷_ : A → List A → List A

pattern [_] x = x ∷ []

module _ {a} {A : Set a} where

  _++_ : List A → List A → List A
  []       ++ ys = ys
  (x ∷ xs) ++ ys = x ∷ (xs ++ ys)

  variable
    x y z : A
    @0 xs ys zs : List A

  data FSet : List A → Set a where
    ∅   : FSet []
    _∪_ : FSet xs → FSet ys → FSet (xs ++ ys)
    sg  : (x : A) → FSet [ x ]
    -- x is forced here, but this is not wanted.
    -- We need a way to tell the forcing machinery to not erase x.

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
