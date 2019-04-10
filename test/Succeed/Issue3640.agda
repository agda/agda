-- Andreas, 2019-03-25, issue #3640, reported by gallais

{-# OPTIONS --sized-types #-}

-- {-# OPTIONS -v tc.polarity:40 #-}

module _ where

open import Agda.Builtin.Size

module M (_ : Set) where
  data U : Size → Set where
    node : ∀ {i} → U (↑ i)

module L (A B : Set) where
  open M A

-- WAS: crash because of number of parameters in size-index checki
-- of L.U was wrongly calculated.

-- Should succeed.
