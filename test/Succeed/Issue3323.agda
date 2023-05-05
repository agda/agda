-- Andreas, 2018-10-27, issue #3323, reported by Guillaume Brunerie
--
-- Mismatches between original and repeated parameter list
-- should not lead to internal errors.

{-# OPTIONS --erasure #-}

open import Agda.Builtin.Bool
open import Agda.Builtin.Equality

data T .(b : Bool) : Set
data T b where  -- Omission of relevance info allowed
  c : Bool → T b

test : ∀{b b'} → T b ≡ T b'
test = refl

-- Should succeed.

record R (@0 b : Bool) : Set
record R b where
  field foo : Bool

-- Should succeed.
