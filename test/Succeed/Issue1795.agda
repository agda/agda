-- Andreas, 2016-01-22
-- special size checking j : Size< i |- j : Size< ↑ j
-- was missing from checkInternal

-- {-# OPTIONS -v tc.polarity:10 #-}
-- {-# OPTIONS -v tc.with.type:50 #-}
-- {-# OPTIONS -v tc.check.internal:30 -v tc.infer.internal:30 #-}

{-# OPTIONS --sized-types #-}

open import Common.Unit
open import Common.Size

postulate
  axiom : Unit
  anything : ∀{A : Set} → A

-- An inductive-coinductive unit type.

mutual

  record IC i : Set where
    coinductive
    field force : ∀(j : Size< i) → IC' j

  data IC' i : Set where
    cons : (xs : IC i) → IC' i -- necessary

-- The recursive identity on IC.

mutual

  idIC  : ∀ i (p : IC i) → IC  i
  IC.force (idIC i p) j = idIC' (↑ j) j (IC.force p j)
    -- (↑ j) is triggering the error
    -- if we write i here, things work

  idIC' : ∀ i (j : Size< i) (p : IC' j) → IC' j
  idIC' i j (cons p) = cons (idIC j p)

-- An inhabitant defined using with.

-- some : ∀ i  → IC i
-- IC.force (some i) j with axiom   -- with is necessary here!
-- ... | unit  = cons (some j)

some  : ∀ i  → IC i
some' : ∀ i (j : Size< i) (u : Unit) → IC' j

IC.force (some i) j = some' i j axiom
some' i j unit  = cons (some j)

-- A coindutive predicate with non-linear use of size i.

mutual

  -- use of i in IC i is necessary, works with IC ∞
  record All i (s : IC i) : Set where
    coinductive
    field force : ∀(j : Size< i) → All' j (IC.force s j)

  data All' i : (s : IC' i) → Set where

-- With abstracted type is well-formed.
-- This means the type-checker can deal with it.

Test : Set₄
Test = (w : Set₃) (i : Size) (j : Size< i) →
       All' j (idIC' (↑ j) j (some' i j axiom))

-- Agda claims: With abstracted type is ill-formed.
-- This means that checkInternal cannot deal with it.

test : ∀ i → All i (idIC i (some i))
All.force (test i) j with Set₂  -- any with expression does it here
... | w = anything

-- i !=< ↑ j of type Size
-- when checking that the type
-- (w : Set₃) (i : Size) (j : Size< i) →
-- All' j (idIC' (↑ j) j (some' i j axiom))
-- of the generated with function is well-formed

{-
candidate type:
  (w : Set₃) (i : Size) (j : Size< i) →
  All' j (idIC' (↑ j) j (some' i j axiom))
candidate type:
  El {_getSort = Type (Max [ClosedLevel 4]), unEl =
  Pi []r(El {_getSort = Type (Max [ClosedLevel 4]), unEl =
    Sort (Type (Max [ClosedLevel 3]))}) (Abs "w"
  El {_getSort = Type (Max []), unEl =
  Pi []r(El {_getSort = SizeUniv, unEl =
    Def Common.Size.Size []}) (Abs "i"
  El {_getSort = Type (Max []), unEl =
  Pi []r(El {_getSort = SizeUniv, unEl =
    Def Common.Size.Size<_ [Apply []?(Var 0 [])]}) (Abs "j"
  El {_getSort = Type (Max []), unEl =
  Def Issue1795.All' [Apply []r(Var 0 []),Apply []r(
    Def Issue1795.idIC' [Apply []r(Def Common.Size.↑_ [Apply []r(Var 0 [])]),Apply []r(Var 0 []),Apply []r(
      Def Issue1795.some' [Apply []r(Var 1 []),Apply []r(Var 0 []),Apply []r(
        Def Issue1795.axiom [])])])]})})})}

Last words:
type t =  (j : Size< (↑ j)) → IC' j → IC' j
self =  idIC' (↑ j)
eliminated by e =  $ j
checking internal  j  :  Size< (↑ j)
checking spine  ( j  :  Size< i ) []  :  Size< (↑ j)
-}
