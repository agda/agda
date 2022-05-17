-- Andreas, 2015-06-29 constructors should be covariant.
-- They are already treated as strictly positive in the positivity checker.

-- {-# OPTIONS -v tc.polarity:20 -v tc.proj.like:10 #-}
-- {-# OPTIONS -v tc.conv.elim:25 -v tc.conv.atom:30 -v tc.conv.term:30 --show-implicit #-}

{-# OPTIONS --sized-types #-}

open import Common.Size
open import Common.Product

-- U (i : contravariant)
record U (i : Size) : Set where
  coinductive
  field out : (j : Size< i) → U j

record Tup (P : Set × Set) : Set where
  constructor tup
  field
    fst : proj₁ P
    snd : proj₂ P

Dup : Set → Set
Dup X = Tup (X , X)

-- This is accepted, as constructors are taken as monotone.
data D : Set where
  c : Dup D → D

fine : ∀{i} → Dup (U ∞) → Dup (U i)
fine (tup x y) = tup x y

-- This should also be accepted.
-- (Additionally, it is the η-short form of fine.)
cast : ∀{i} → Dup (U ∞) → Dup (U i)
cast x = x
