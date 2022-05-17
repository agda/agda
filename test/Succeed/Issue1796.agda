-- Andreas, 2016-01-23, issue 1796
-- Need to run size constraint solver before with-abstraction

-- {-# OPTIONS -v tc.size:100 -v tc.meta.assign:30 #-}

{-# OPTIONS --sized-types #-}

open import Common.Size

postulate
  anything : ∀{A : Set} → A

mutual

  record IO i : Set where
    coinductive
    field force : ∀{j : Size< i} → IO' j

  data IO' i : Set where
    cons : IO i → IO' i

mutual

  record All i (s : IO ∞) : Set where
    field force : ∀{j : Size< i} → All' j (IO.force s)

  data All' i : (s : IO' ∞) → Set where
    always  : ∀ e → All' i (cons e)

runIO  : ∀{i} (s : IO ∞) → IO i
IO.force (runIO s) with IO.force s
... | cons e = cons e

-- With abstraction fails when _ in IO.force s {_}
-- has not been solved to ∞.

test : ∀ i s → All i (runIO s)
All.force (test i s) with IO.force s -- works with {∞} added
All.force (test i s) | cons e = always e

-- cons e != IO.force (runIO {∞} s) {∞} | IO.force s of type IO' ∞
-- when checking that the expression always e has type
-- All' .j (IO.force (runIO {∞} s) {∞} | IO.force s)
