-- Andreas, 2017-10-11, issue #2796

-- A failed check for projection-likeness
-- made the overloaded projection not resolve.

-- {-# OPTIONS -v tc.proj.like:100 #-}
-- {-# OPTIONS -v tc.proj.amb:100 #-}

postulate
  L     : Set
  lzero : L
  Type  : L → Set
  El    : ∀{l} → Type l → Set

record Pred (A : Set) l : Set where  -- Works without l
  field
    app : A → Type l

record Sub l : Set1 where
  field
    Carrier : Set
    pred    : Pred Carrier l
  open Pred pred public

open Pred   -- Works without this (of course)
open Sub

test : (S T : Sub lzero) → (f : S .Carrier → T .Carrier) → Set
test S T f = (a : S .Carrier) → El (S .app a) → El (T .app (f a))

-- Problem WAS:
-- Cannot resolve overloaded projection app because no matching candidate found
-- when checking that the expression S .app a has type
-- Type (_l_22 S T f a)

-- Should succeed.
