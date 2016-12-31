-- Andrease, 2016-12-31, issue #1975 reported by nad.

-- {-# OPTIONS -v tc.lhs.split:40 #-}

data ⊥ : Set where

record ⊤ : Set where

data Bool : Set where
  true false : Bool

T : Bool → Set
T false = ⊥
T true  = ⊤

module M (b : Bool) where

  data D : Set where
    c : T b → D

open M true

-- The following definition is rejected:

-- rejected : M.D false → ⊥
-- rejected (c x) = x

data D₂ : Set where
  c : D₂

-- WAS: However, the following definition is accepted:

test : M.D false → ⊥
test (c x) = x

-- I think both definitions should be rejected.
-- NOW: Both are rejected.
