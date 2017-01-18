-- Andreas, 2017-01-18, issue #2408

-- DLubs were not serialized, thus, there was a problem with
-- level dependent on irrelevant values.

{-# OPTIONS --show-irrelevant #-}

-- {-# OPTIONS -v tc:70 #-}

open import Agda.Primitive

postulate
  A : Set
  l : .(a : A) → Level
  F : .(a : A) → Set (l a)

-- checked type signature
--   F : .(a : A) → Set (l a)
--   of sort  dLub Set (λ a → Set (lsuc (l a)))
